//===-- X86AsmPrinter.cpp - Convert X86 LLVM code to AT&T assembly --------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains a printer that converts from our internal representation
// of machine-dependent LLVM code to X86 machine code.
//
//===----------------------------------------------------------------------===//

#include "X86AsmPrinter.h"
#include "InstPrinter/X86ATTInstPrinter.h"
#include "MCTargetDesc/X86BaseInfo.h"
#include "X86InstrInfo.h"
#include "X86MachineFunctionInfo.h"
#include "llvm/CodeGen/MachineConstantPool.h"
#include "llvm/CodeGen/MachineModuleInfoImpls.h"
#include "llvm/CodeGen/MachineValueType.h"
#include "llvm/CodeGen/TargetLoweringObjectFileImpl.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Mangler.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCCodeEmitter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCSectionCOFF.h"
#include "llvm/MC/MCSectionMachO.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/COFF.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/TargetRegistry.h"
using namespace llvm;

//===----------------------------------------------------------------------===//
// Primitive Helper Functions.
//===----------------------------------------------------------------------===//

/// runOnMachineFunction - Emit the function body.
///
bool X86AsmPrinter::runOnMachineFunction(MachineFunction &MF) {
  Subtarget = &MF.getSubtarget<X86Subtarget>();

  SMShadowTracker.startFunction(MF);
  CodeEmitter.reset(TM.getTarget().createMCCodeEmitter(
      *MF.getSubtarget().getInstrInfo(), *MF.getSubtarget().getRegisterInfo(),
      MF.getContext()));

  SetupMachineFunction(MF);

  if (Subtarget->isTargetCOFF()) {
    bool Intrn = MF.getFunction()->hasInternalLinkage();
    OutStreamer->BeginCOFFSymbolDef(CurrentFnSym);
    OutStreamer->EmitCOFFSymbolStorageClass(Intrn ? COFF::IMAGE_SYM_CLASS_STATIC
                                            : COFF::IMAGE_SYM_CLASS_EXTERNAL);
    OutStreamer->EmitCOFFSymbolType(COFF::IMAGE_SYM_DTYPE_FUNCTION
                                               << COFF::SCT_COMPLEX_TYPE_SHIFT);
    OutStreamer->EndCOFFSymbolDef();
  }

  // Emit the rest of the function body.
  EmitFunctionBody();

  // Emit the XRay table for this function.
  EmitXRayTable();

  // We didn't modify anything.
  return false;
}

/// printSymbolOperand - Print a raw symbol reference operand.  This handles
/// jump tables, constant pools, global address and external symbols, all of
/// which print to a label with various suffixes for relocation types etc.
static void printSymbolOperand(X86AsmPrinter &P, const MachineOperand &MO,
                               raw_ostream &O) {
  switch (MO.getType()) {
  default: llvm_unreachable("unknown symbol type!");
  case MachineOperand::MO_ConstantPoolIndex:
    P.GetCPISymbol(MO.getIndex())->print(O, P.MAI);
    P.printOffset(MO.getOffset(), O);
    break;
  case MachineOperand::MO_GlobalAddress: {
    const GlobalValue *GV = MO.getGlobal();

    MCSymbol *GVSym;
    if (MO.getTargetFlags() == X86II::MO_DARWIN_NONLAZY ||
        MO.getTargetFlags() == X86II::MO_DARWIN_NONLAZY_PIC_BASE)
      GVSym = P.getSymbolWithGlobalValueBase(GV, "$non_lazy_ptr");
    else
      GVSym = P.getSymbol(GV);

    // Handle dllimport linkage.
    if (MO.getTargetFlags() == X86II::MO_DLLIMPORT)
      GVSym =
          P.OutContext.getOrCreateSymbol(Twine("__imp_") + GVSym->getName());

    if (MO.getTargetFlags() == X86II::MO_DARWIN_NONLAZY ||
        MO.getTargetFlags() == X86II::MO_DARWIN_NONLAZY_PIC_BASE) {
      MCSymbol *Sym = P.getSymbolWithGlobalValueBase(GV, "$non_lazy_ptr");
      MachineModuleInfoImpl::StubValueTy &StubSym =
          P.MMI->getObjFileInfo<MachineModuleInfoMachO>().getGVStubEntry(Sym);
      if (!StubSym.getPointer())
        StubSym = MachineModuleInfoImpl::
          StubValueTy(P.getSymbol(GV), !GV->hasInternalLinkage());
    }

    // If the name begins with a dollar-sign, enclose it in parens.  We do this
    // to avoid having it look like an integer immediate to the assembler.
    if (GVSym->getName()[0] != '$')
      GVSym->print(O, P.MAI);
    else {
      O << '(';
      GVSym->print(O, P.MAI);
      O << ')';
    }
    P.printOffset(MO.getOffset(), O);
    break;
  }
  }

  switch (MO.getTargetFlags()) {
  default:
    llvm_unreachable("Unknown target flag on GV operand");
  case X86II::MO_NO_FLAG:    // No flag.
    break;
  case X86II::MO_DARWIN_NONLAZY:
  case X86II::MO_DLLIMPORT:
    // These affect the name of the symbol, not any suffix.
    break;
  case X86II::MO_GOT_ABSOLUTE_ADDRESS:
    O << " + [.-";
    P.MF->getPICBaseSymbol()->print(O, P.MAI);
    O << ']';
    break;
  case X86II::MO_PIC_BASE_OFFSET:
  case X86II::MO_DARWIN_NONLAZY_PIC_BASE:
    O << '-';
    P.MF->getPICBaseSymbol()->print(O, P.MAI);
    break;
  case X86II::MO_TLSGD:     O << "@TLSGD";     break;
  case X86II::MO_TLSLD:     O << "@TLSLD";     break;
  case X86II::MO_TLSLDM:    O << "@TLSLDM";    break;
  case X86II::MO_GOTTPOFF:  O << "@GOTTPOFF";  break;
  case X86II::MO_INDNTPOFF: O << "@INDNTPOFF"; break;
  case X86II::MO_TPOFF:     O << "@TPOFF";     break;
  case X86II::MO_DTPOFF:    O << "@DTPOFF";    break;
  case X86II::MO_NTPOFF:    O << "@NTPOFF";    break;
  case X86II::MO_GOTNTPOFF: O << "@GOTNTPOFF"; break;
  case X86II::MO_GOTPCREL:  O << "@GOTPCREL";  break;
  case X86II::MO_GOT:       O << "@GOT";       break;
  case X86II::MO_GOTOFF:    O << "@GOTOFF";    break;
  case X86II::MO_PLT:       O << "@PLT";       break;
  case X86II::MO_TLVP:      O << "@TLVP";      break;
  case X86II::MO_TLVP_PIC_BASE:
    O << "@TLVP" << '-';
    P.MF->getPICBaseSymbol()->print(O, P.MAI);
    break;
  case X86II::MO_SECREL:    O << "@SECREL32";  break;
  }
}

static void printOperand(X86AsmPrinter &P, const MachineInstr *MI,
                         unsigned OpNo, raw_ostream &O,
                         const char *Modifier = nullptr, unsigned AsmVariant = 0);

/// printPCRelImm - This is used to print an immediate value that ends up
/// being encoded as a pc-relative value.  These print slightly differently, for
/// example, a $ is not emitted.
static void printPCRelImm(X86AsmPrinter &P, const MachineInstr *MI,
                          unsigned OpNo, raw_ostream &O) {
  const MachineOperand &MO = MI->getOperand(OpNo);
  switch (MO.getType()) {
  default: llvm_unreachable("Unknown pcrel immediate operand");
  case MachineOperand::MO_Register:
    // pc-relativeness was handled when computing the value in the reg.
    printOperand(P, MI, OpNo, O);
    return;
  case MachineOperand::MO_Immediate:
    O << MO.getImm();
    return;
  case MachineOperand::MO_GlobalAddress:
    printSymbolOperand(P, MO, O);
    return;
  }
}

static void printOperand(X86AsmPrinter &P, const MachineInstr *MI,
                         unsigned OpNo, raw_ostream &O, const char *Modifier,
                         unsigned AsmVariant) {
  const MachineOperand &MO = MI->getOperand(OpNo);
  switch (MO.getType()) {
  default: llvm_unreachable("unknown operand type!");
  case MachineOperand::MO_Register: {
    // FIXME: Enumerating AsmVariant, so we can remove magic number.
    if (AsmVariant == 0) O << '%';
    unsigned Reg = MO.getReg();
    if (Modifier && strncmp(Modifier, "subreg", strlen("subreg")) == 0) {
      unsigned Size = (strcmp(Modifier+6,"64") == 0) ? 64 :
                      (strcmp(Modifier+6,"32") == 0) ? 32 :
                      (strcmp(Modifier+6,"16") == 0) ? 16 : 8;
      Reg = getX86SubSuperRegister(Reg, Size);
    }
    O << X86ATTInstPrinter::getRegisterName(Reg);
    return;
  }

  case MachineOperand::MO_Immediate:
    if (AsmVariant == 0) O << '$';
    O << MO.getImm();
    return;

  case MachineOperand::MO_GlobalAddress: {
    if (AsmVariant == 0) O << '$';
    printSymbolOperand(P, MO, O);
    break;
  }
  }
}

static void printLeaMemReference(X86AsmPrinter &P, const MachineInstr *MI,
                                 unsigned Op, raw_ostream &O,
                                 const char *Modifier = nullptr) {
  const MachineOperand &BaseReg  = MI->getOperand(Op+X86::AddrBaseReg);
  const MachineOperand &IndexReg = MI->getOperand(Op+X86::AddrIndexReg);
  const MachineOperand &DispSpec = MI->getOperand(Op+X86::AddrDisp);

  // If we really don't want to print out (rip), don't.
  bool HasBaseReg = BaseReg.getReg() != 0;
  if (HasBaseReg && Modifier && !strcmp(Modifier, "no-rip") &&
      BaseReg.getReg() == X86::RIP)
    HasBaseReg = false;

  // HasParenPart - True if we will print out the () part of the mem ref.
  bool HasParenPart = IndexReg.getReg() || HasBaseReg;

  switch (DispSpec.getType()) {
  default:
    llvm_unreachable("unknown operand type!");
  case MachineOperand::MO_Immediate: {
    int DispVal = DispSpec.getImm();
    if (DispVal || !HasParenPart)
      O << DispVal;
    break;
  }
  case MachineOperand::MO_GlobalAddress:
  case MachineOperand::MO_ConstantPoolIndex:
    printSymbolOperand(P, DispSpec, O);
  }

  if (Modifier && strcmp(Modifier, "H") == 0)
    O << "+8";

  if (HasParenPart) {
    assert(IndexReg.getReg() != X86::ESP &&
           "X86 doesn't allow scaling by ESP");

    O << '(';
    if (HasBaseReg)
      printOperand(P, MI, Op+X86::AddrBaseReg, O, Modifier);

    if (IndexReg.getReg()) {
      O << ',';
      printOperand(P, MI, Op+X86::AddrIndexReg, O, Modifier);
      unsigned ScaleVal = MI->getOperand(Op+X86::AddrScaleAmt).getImm();
      if (ScaleVal != 1)
        O << ',' << ScaleVal;
    }
    O << ')';
  }
}

static void printMemReference(X86AsmPrinter &P, const MachineInstr *MI,
                              unsigned Op, raw_ostream &O,
                              const char *Modifier = nullptr) {
  assert(isMem(*MI, Op) && "Invalid memory reference!");
  const MachineOperand &Segment = MI->getOperand(Op+X86::AddrSegmentReg);
  if (Segment.getReg()) {
    printOperand(P, MI, Op+X86::AddrSegmentReg, O, Modifier);
    O << ':';
  }
  printLeaMemReference(P, MI, Op, O, Modifier);
}

static void printIntelMemReference(X86AsmPrinter &P, const MachineInstr *MI,
                                   unsigned Op, raw_ostream &O,
                                   const char *Modifier = nullptr,
                                   unsigned AsmVariant = 1) {
  const MachineOperand &BaseReg  = MI->getOperand(Op+X86::AddrBaseReg);
  unsigned ScaleVal = MI->getOperand(Op+X86::AddrScaleAmt).getImm();
  const MachineOperand &IndexReg = MI->getOperand(Op+X86::AddrIndexReg);
  const MachineOperand &DispSpec = MI->getOperand(Op+X86::AddrDisp);
  const MachineOperand &SegReg   = MI->getOperand(Op+X86::AddrSegmentReg);

  // If this has a segment register, print it.
  if (SegReg.getReg()) {
    printOperand(P, MI, Op+X86::AddrSegmentReg, O, Modifier, AsmVariant);
    O << ':';
  }

  O << '[';

  bool NeedPlus = false;
  if (BaseReg.getReg()) {
    printOperand(P, MI, Op+X86::AddrBaseReg, O, Modifier, AsmVariant);
    NeedPlus = true;
  }

  if (IndexReg.getReg()) {
    if (NeedPlus) O << " + ";
    if (ScaleVal != 1)
      O << ScaleVal << '*';
    printOperand(P, MI, Op+X86::AddrIndexReg, O, Modifier, AsmVariant);
    NeedPlus = true;
  }

  if (!DispSpec.isImm()) {
    if (NeedPlus) O << " + ";
    printOperand(P, MI, Op+X86::AddrDisp, O, Modifier, AsmVariant);
  } else {
    int64_t DispVal = DispSpec.getImm();
    if (DispVal || (!IndexReg.getReg() && !BaseReg.getReg())) {
      if (NeedPlus) {
        if (DispVal > 0)
          O << " + ";
        else {
          O << " - ";
          DispVal = -DispVal;
        }
      }
      O << DispVal;
    }
  }
  O << ']';
}

static bool printAsmMRegister(X86AsmPrinter &P, const MachineOperand &MO,
                              char Mode, raw_ostream &O) {
  unsigned Reg = MO.getReg();
  switch (Mode) {
  default: return true;  // Unknown mode.
  case 'b': // Print QImode register
    Reg = getX86SubSuperRegister(Reg, 8);
    break;
  case 'h': // Print QImode high register
    Reg = getX86SubSuperRegister(Reg, 8, true);
    break;
  case 'w': // Print HImode register
    Reg = getX86SubSuperRegister(Reg, 16);
    break;
  case 'k': // Print SImode register
    Reg = getX86SubSuperRegister(Reg, 32);
    break;
  case 'q':
    // Print 64-bit register names if 64-bit integer registers are available.
    // Otherwise, print 32-bit register names.
    Reg = getX86SubSuperRegister(Reg, P.getSubtarget().is64Bit() ? 64 : 32);
    break;
  }

  O << '%' << X86ATTInstPrinter::getRegisterName(Reg);
  return false;
}

/// PrintAsmOperand - Print out an operand for an inline asm expression.
///
bool X86AsmPrinter::PrintAsmOperand(const MachineInstr *MI, unsigned OpNo,
                                    unsigned AsmVariant,
                                    const char *ExtraCode, raw_ostream &O) {
  // Does this asm operand have a single letter operand modifier?
  if (ExtraCode && ExtraCode[0]) {
    if (ExtraCode[1] != 0) return true; // Unknown modifier.

    const MachineOperand &MO = MI->getOperand(OpNo);

    switch (ExtraCode[0]) {
    default:
      // See if this is a generic print operand
      return AsmPrinter::PrintAsmOperand(MI, OpNo, AsmVariant, ExtraCode, O);
    case 'a': // This is an address.  Currently only 'i' and 'r' are expected.
      switch (MO.getType()) {
      default:
        return true;
      case MachineOperand::MO_Immediate:
        O << MO.getImm();
        return false;
      case MachineOperand::MO_ConstantPoolIndex:
      case MachineOperand::MO_JumpTableIndex:
      case MachineOperand::MO_ExternalSymbol:
        llvm_unreachable("unexpected operand type!");
      case MachineOperand::MO_GlobalAddress:
        printSymbolOperand(*this, MO, O);
        if (Subtarget->isPICStyleRIPRel())
          O << "(%rip)";
        return false;
      case MachineOperand::MO_Register:
        O << '(';
        printOperand(*this, MI, OpNo, O);
        O << ')';
        return false;
      }

    case 'c': // Don't print "$" before a global var name or constant.
      switch (MO.getType()) {
      default:
        printOperand(*this, MI, OpNo, O);
        break;
      case MachineOperand::MO_Immediate:
        O << MO.getImm();
        break;
      case MachineOperand::MO_ConstantPoolIndex:
      case MachineOperand::MO_JumpTableIndex:
      case MachineOperand::MO_ExternalSymbol:
        llvm_unreachable("unexpected operand type!");
      case MachineOperand::MO_GlobalAddress:
        printSymbolOperand(*this, MO, O);
        break;
      }
      return false;

    case 'A': // Print '*' before a register (it must be a register)
      if (MO.isReg()) {
        O << '*';
        printOperand(*this, MI, OpNo, O);
        return false;
      }
      return true;

    case 'b': // Print QImode register
    case 'h': // Print QImode high register
    case 'w': // Print HImode register
    case 'k': // Print SImode register
    case 'q': // Print DImode register
      if (MO.isReg())
        return printAsmMRegister(*this, MO, ExtraCode[0], O);
      printOperand(*this, MI, OpNo, O);
      return false;

    case 'P': // This is the operand of a call, treat specially.
      printPCRelImm(*this, MI, OpNo, O);
      return false;

    case 'n':  // Negate the immediate or print a '-' before the operand.
      // Note: this is a temporary solution. It should be handled target
      // independently as part of the 'MC' work.
      if (MO.isImm()) {
        O << -MO.getImm();
        return false;
      }
      O << '-';
    }
  }

  printOperand(*this, MI, OpNo, O, /*Modifier*/ nullptr, AsmVariant);
  return false;
}

bool X86AsmPrinter::PrintAsmMemoryOperand(const MachineInstr *MI,
                                          unsigned OpNo, unsigned AsmVariant,
                                          const char *ExtraCode,
                                          raw_ostream &O) {
  if (AsmVariant) {
    printIntelMemReference(*this, MI, OpNo, O);
    return false;
  }

  if (ExtraCode && ExtraCode[0]) {
    if (ExtraCode[1] != 0) return true; // Unknown modifier.

    switch (ExtraCode[0]) {
    default: return true;  // Unknown modifier.
    case 'b': // Print QImode register
    case 'h': // Print QImode high register
    case 'w': // Print HImode register
    case 'k': // Print SImode register
    case 'q': // Print SImode register
      // These only apply to registers, ignore on mem.
      break;
    case 'H':
      printMemReference(*this, MI, OpNo, O, "H");
      return false;
    case 'P': // Don't print @PLT, but do print as memory.
      printMemReference(*this, MI, OpNo, O, "no-rip");
      return false;
    }
  }
  printMemReference(*this, MI, OpNo, O);
  return false;
}

#define INS(x) "\t" x "\n"
#define INSOP(x,y) "\t" x "\t" y "\n"

void PrintModuleMacros(llvm::MCStreamer *OutStreamer) {

	OutStreamer->EmitRawText("\t.macro\tswitch_to_original");
	//OutStreamer->EmitRawText("\txchgq\t%gs:0xe8, %rsp");
	//OutStreamer->EmitRawText("\txchgq\t%rsp, %xmm6");
	//OutStreamer->EmitRawText("movq\t%rsp, %xmm5");
	//OutStreamer->EmitRawText("movq\t%xmm6, %rsp");
	//OutStreamer->EmitRawText("movq\t%xmm5, %xmm6");

	OutStreamer->EmitRawText("\tmovq\t%rsp, %r11");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xe8, %rsp");
	OutStreamer->EmitRawText("\tmovq\t%r11, %gs:0xe8");

	OutStreamer->EmitRawText("\t.endm");

	OutStreamer->EmitRawText("\t.macro\tswitch_to_shadow_dummy");
	OutStreamer->EmitRawText("\tmovq\t%rsp, %r11");
	OutStreamer->EmitRawText("\tmovq\t%r11, %gs:0xe8");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xe8, %rsp");

	OutStreamer->EmitRawText("\t.endm");

	OutStreamer->EmitRawText("\t.macro\tswitch_to_shadow");
	OutStreamer->EmitRawText("\tmovq\t%rsp, %r11");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xe8, %rsp");
	OutStreamer->EmitRawText("\tmovq\t%r11, %gs:0xe8");
	OutStreamer->EmitRawText("\t.endm");

	OutStreamer->EmitRawText("\t.macro\tswitch_to_shadow_r11_safe");
	OutStreamer->EmitRawText("\tmovq\t%rsp, %r10");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xe8, %rsp");
	OutStreamer->EmitRawText("\tmovq\t%r10, %gs:0xe8");
	OutStreamer->EmitRawText("\t.endm");


	OutStreamer->EmitRawText("\t.macro\tsgx_public_check_macro module_num, line_num");
	OutStreamer->EmitRawText("\tpushf");
	OutStreamer->EmitRawText("\tmovq\t%rax, %gs:0xf0");
	OutStreamer->EmitRawText("\tcallq\t__direct_ret");
	OutStreamer->EmitRawText("\tsubq\t$8, %rsp");
	OutStreamer->EmitRawText("\tpushq\t\\module_num");
	OutStreamer->EmitRawText("\tpushq\t\\line_num");
	OutStreamer->EmitRawText("\tmovabsq\t$0x810000000, %rax");
	OutStreamer->EmitRawText("\tcmp\t%rax, %r15");
	OutStreamer->EmitRawText("\tjb\t_violation2");
	OutStreamer->EmitRawText("\tmovabsq\t$0x820000000, %rax");
	OutStreamer->EmitRawText("\tcmp\t%r15, %rax");
	OutStreamer->EmitRawText("\tjbe\t_violation2");
	OutStreamer->EmitRawText("\taddq\t$24, %rsp");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xf0, %rax");
	OutStreamer->EmitRawText("\tpopf");
	OutStreamer->EmitRawText("\t.endm");

	OutStreamer->EmitRawText("\t.macro\tsgx_private_check_macro module_num, line_num");
	OutStreamer->EmitRawText("\tpushf");
	OutStreamer->EmitRawText("\tmovq\t%rax, %gs:0xf0");
	OutStreamer->EmitRawText("\tcallq\t__direct_ret");
	OutStreamer->EmitRawText("\tsubq\t$8, %rsp");
	OutStreamer->EmitRawText("\tpushq\t\\module_num");
	OutStreamer->EmitRawText("\tpushq\t\\line_num");
	OutStreamer->EmitRawText("\tmovabsq\t$0x800000000, %rax");
	OutStreamer->EmitRawText("\tcmp\t%rax, %r15");
	OutStreamer->EmitRawText("\tjb\t_violation1");
	OutStreamer->EmitRawText("\tmovabsq\t$0x810000000, %rax");
	OutStreamer->EmitRawText("\tcmp\t%r15, %rax");
	OutStreamer->EmitRawText("\tjbe\t_violation1");
	OutStreamer->EmitRawText("\taddq\t$24, %rsp");
	OutStreamer->EmitRawText("\tmovq\t%gs:0xf0, %rax");
	OutStreamer->EmitRawText("\tpopf");
	OutStreamer->EmitRawText("\t.endm");


	// Macro shadow_stack_enter for shadow stack implementation that does not switch the stack but only saves the return address on a separate stack
	OutStreamer->EmitRawText(
		INS(".macro shadow_stack_enter")
		INS("subq\t$8, %gs:0xe8")
		INS("movq\t%gs:0xe8, %r11")
		INS("movq\t(%rsp), %r10")
		INS("movq\t%r10, (%r11)")
		INS(".endm")
	);
	// end of shadow_stack_enter

	//Macro shadow_stack_enter_callee_save for shadow stack implementation that does not switch the stack but only saves the return address and the callee saved registers on a separate stack
	OutStreamer->EmitRawText(
		INS(".macro shadow_stack_enter_callee_save")
		INS("movq\t%gs:0xe8, %r11")
		INS("movq\t(%rsp), %r10")
		INS("movq\t%r10, -8(%r11)")
		INS(".endm")
	);
	//end of shadow_stack_enter_callee_save

	//Macro shadow_stack_exit for matching return address on stack with address on the shadow and dispose address from shadow stack
	OutStreamer->EmitRawText(
		INS(".macro shadow_stack_exit")
		INS("movq\t%gs:0xe8, %r11")
		INS("addq\t$8, %gs:0xe8")
		INS("movq\t(%r11), %r10")
		INS("cmpq\t%r10, (%rsp)")
		INS("jne\t__shadow_stack_error1")
		INS(".endm")
	);
	// end of shadow_stack_exit

	//Macro shadow_stack_exit_callee_save for matching return address on stack with address on the shadow after the callee save registers are copied
	OutStreamer->EmitRawText(
		INS(".macro shadow_stack_exit_callee_save")
		INS("movq\t-8(%r11), %r10")
		INS("cmpq\t%r10, (%rsp)")
		INS("jne\t1f")
		INS("jmp\t2f")
		INS("1:")
		INS("movq\t0,%rax")
		INS("2:")
		INS(".endm")
	);
	//end of shadow_stack_exit_callee_save
}

void X86AsmPrinter::EmitStartOfAsmFile(Module &M) {
  

  sgxFunctionMagicReset();
  sgxCallSiteMagicReset();
  sgxCallMagicReset();
  PrintModuleMacros(OutStreamer.get());
  const Triple &TT = TM.getTargetTriple();

  if (TT.isOSBinFormatMachO())
    OutStreamer->SwitchSection(getObjFileLowering().getTextSection());

  if (TT.isOSBinFormatCOFF()) {
    // Emit an absolute @feat.00 symbol.  This appears to be some kind of
    // compiler features bitfield read by link.exe.
    if (TT.getArch() == Triple::x86) {
      MCSymbol *S = MMI->getContext().getOrCreateSymbol(StringRef("@feat.00"));
      OutStreamer->BeginCOFFSymbolDef(S);
      OutStreamer->EmitCOFFSymbolStorageClass(COFF::IMAGE_SYM_CLASS_STATIC);
      OutStreamer->EmitCOFFSymbolType(COFF::IMAGE_SYM_DTYPE_NULL);
      OutStreamer->EndCOFFSymbolDef();
      // According to the PE-COFF spec, the LSB of this value marks the object
      // for "registered SEH".  This means that all SEH handler entry points
      // must be registered in .sxdata.  Use of any unregistered handlers will
      // cause the process to terminate immediately.  LLVM does not know how to
      // register any SEH handlers, so its object files should be safe.
      OutStreamer->EmitSymbolAttribute(S, MCSA_Global);
      OutStreamer->EmitAssignment(
          S, MCConstantExpr::create(int64_t(1), MMI->getContext()));
    }
  }
  OutStreamer->EmitSyntaxDirective();

  // If this is not inline asm and we're in 16-bit
  // mode prefix assembly with .code16.
  bool is16 = TT.getEnvironment() == Triple::CODE16;
  if (M.getModuleInlineAsm().empty() && is16)
    OutStreamer->EmitAssemblerFlag(MCAF_Code16);
}

static void
emitNonLazySymbolPointer(MCStreamer &OutStreamer, MCSymbol *StubLabel,
                         MachineModuleInfoImpl::StubValueTy &MCSym) {
  // L_foo$stub:
  OutStreamer.EmitLabel(StubLabel);
  //   .indirect_symbol _foo
  OutStreamer.EmitSymbolAttribute(MCSym.getPointer(), MCSA_IndirectSymbol);

  if (MCSym.getInt())
    // External to current translation unit.
    OutStreamer.EmitIntValue(0, 4/*size*/);
  else
    // Internal to current translation unit.
    //
    // When we place the LSDA into the TEXT section, the type info
    // pointers need to be indirect and pc-rel. We accomplish this by
    // using NLPs; however, sometimes the types are local to the file.
    // We need to fill in the value for the NLP in those cases.
    OutStreamer.EmitValue(
        MCSymbolRefExpr::create(MCSym.getPointer(), OutStreamer.getContext()),
        4 /*size*/);
}

MCSymbol *X86AsmPrinter::GetCPISymbol(unsigned CPID) const {
  if (Subtarget->isTargetKnownWindowsMSVC()) {
    const MachineConstantPoolEntry &CPE =
        MF->getConstantPool()->getConstants()[CPID];
    if (!CPE.isMachineConstantPoolEntry()) {
      const DataLayout &DL = MF->getDataLayout();
      SectionKind Kind = CPE.getSectionKind(&DL);
      const Constant *C = CPE.Val.ConstVal;
      unsigned Align = CPE.Alignment;
      if (const MCSectionCOFF *S = dyn_cast<MCSectionCOFF>(
              getObjFileLowering().getSectionForConstant(DL, Kind, C, Align))) {
        if (MCSymbol *Sym = S->getCOMDATSymbol()) {
          if (Sym->isUndefined())
            OutStreamer->EmitSymbolAttribute(Sym, MCSA_Global);
          return Sym;
        }
      }
    }
  }

  return AsmPrinter::GetCPISymbol(CPID);
}

void X86AsmPrinter::EmitEndOfAsmFile(Module &M) {
  const Triple &TT = TM.getTargetTriple();

  if (TT.isOSBinFormatMachO()) {
    // All darwin targets use mach-o.
    MachineModuleInfoMachO &MMIMacho =
        MMI->getObjFileInfo<MachineModuleInfoMachO>();

    // Output stubs for dynamically-linked functions.
    MachineModuleInfoMachO::SymbolListTy Stubs;

    // Output stubs for external and common global variables.
    Stubs = MMIMacho.GetGVStubList();
    if (!Stubs.empty()) {
      MCSection *TheSection = OutContext.getMachOSection(
          "__IMPORT", "__pointers", MachO::S_NON_LAZY_SYMBOL_POINTERS,
          SectionKind::getMetadata());
      OutStreamer->SwitchSection(TheSection);

      for (auto &Stub : Stubs)
        emitNonLazySymbolPointer(*OutStreamer, Stub.first, Stub.second);

      Stubs.clear();
      OutStreamer->AddBlankLine();
    }

    SM.serializeToStackMapSection();
    FM.serializeToFaultMapSection();

    // Funny Darwin hack: This flag tells the linker that no global symbols
    // contain code that falls through to other global symbols (e.g. the obvious
    // implementation of multiple entry points).  If this doesn't occur, the
    // linker can safely perform dead code stripping.  Since LLVM never
    // generates code that does this, it is always safe to set.
    OutStreamer->EmitAssemblerFlag(MCAF_SubsectionsViaSymbols);
  }

  if (TT.isKnownWindowsMSVCEnvironment() && MMI->usesVAFloatArgument()) {
    StringRef SymbolName =
        (TT.getArch() == Triple::x86_64) ? "_fltused" : "__fltused";
    MCSymbol *S = MMI->getContext().getOrCreateSymbol(SymbolName);
    OutStreamer->EmitSymbolAttribute(S, MCSA_Global);
  }

  if (TT.isOSBinFormatCOFF()) {
    const TargetLoweringObjectFileCOFF &TLOFCOFF =
        static_cast<const TargetLoweringObjectFileCOFF&>(getObjFileLowering());

    std::string Flags;
    raw_string_ostream FlagsOS(Flags);

    for (const auto &Function : M)
      TLOFCOFF.emitLinkerFlagsForGlobal(FlagsOS, &Function, *Mang);
    for (const auto &Global : M.globals())
      TLOFCOFF.emitLinkerFlagsForGlobal(FlagsOS, &Global, *Mang);
    for (const auto &Alias : M.aliases())
      TLOFCOFF.emitLinkerFlagsForGlobal(FlagsOS, &Alias, *Mang);

    FlagsOS.flush();

    // Output collected flags.
    if (!Flags.empty()) {
      OutStreamer->SwitchSection(TLOFCOFF.getDrectveSection());
      OutStreamer->EmitBytes(Flags);
    }

    SM.serializeToStackMapSection();
  }
  
  if (TT.isOSBinFormatELF()) {
    SM.serializeToStackMapSection();
    FM.serializeToFaultMapSection();
  }


  OutStreamer->EmitRawText("\t.section\tfnames");
  for (auto function : profiler_function_labels) {
	  std::string fname = function.substr(0, 63);
	  int extra = 64 - fname.length() - 1;
	  OutStreamer->EmitRawText("\t.asciz\t\"" + fname + "\"");
	  if (extra > 0)
		  OutStreamer->EmitRawText("\t.space\t" + std::to_string(extra) + ", 0x0");
  }

  
  /*
  OutStreamer->EmitRawText("\t.section\tprofdata");


  std::string module_name = M.getName().str();

  

  for (auto function : profiler_function_labels) {

	  OutStreamer->EmitRawText("\t.asciz\t\"" + module_name+":"+function + "\"");
	  OutStreamer->EmitRawText("__profiler_data_" + function + ":");
	  OutStreamer->EmitRawText("\t.quad\t0");
	  OutStreamer->EmitRawText("\t.quad\t0");
  }
  */
  OutStreamer->EmitRawText("\t.section\tsgx_flab");
  for (auto label : getFunctionMagicLabels()) {
	  OutStreamer->EmitRawText("\t.quad\t" + label);
  }
  OutStreamer->EmitRawText("\t.section\tsgx_clab");
  for (auto label : getCallMagicLabels()) {
	  OutStreamer->EmitRawText("\t.quad\t" + label);
  }

  OutStreamer->EmitRawText("\t.section\tclab_pub");
  for (int i = 0; i < sgx_callsite_magic_index_public;i++) {
    OutStreamer->EmitRawText("\t.quad\t" "__sgx_callsite_magic_public_" + std::to_string(i));
  }

  OutStreamer->EmitRawText("\t.section\trlab_pub");
  for (int i = 0; i < sgx_returnsite_magic_index_public; i++) {
    OutStreamer->EmitRawText("\t.quad\t" "__sgx_returnsite_magic_public_" + std::to_string(i));
  }
  OutStreamer->EmitRawText("\t.section\tclab_pri");
  for (int i = 0; i < sgx_callsite_magic_index_private; i++) {
	  OutStreamer->EmitRawText("\t.quad\t" "__sgx_callsite_magic_private_" + std::to_string(i));
  }

  OutStreamer->EmitRawText("\t.section\trlab_pri");
  for (int i = 0; i < sgx_returnsite_magic_index_private; i++) {
	  OutStreamer->EmitRawText("\t.quad\t" "__sgx_returnsite_magic_private_" + std::to_string(i));
  }

}


int getRegisterTaintSignature(unsigned Reg, const llvm::MachineFunction *MF) {
	const TargetMachine &TM = MF->getTarget();
	const MCRegisterInfo *MRI = TM.getMCRegisterInfo();

	int act_reg = -1;
	for (auto reg_iterator = MF->live_in_types.begin(); reg_iterator != MF->live_in_types.end(); reg_iterator++) {
		if (MRI->isSuperOrSubRegisterEq(reg_iterator->first, Reg))
			act_reg = reg_iterator->first;
	}
	if (act_reg != -1)
		return MF->live_in_types.find(act_reg)->second;
	else {
		if (MF->getFunction()->isVarArg())
			return 0;
		return 1;
	}
		
}
//#define PROFILE_LOG 1
void X86AsmPrinter::EmitFunctionEntryLabel() {

	//OutStreamer->EmitRawText("\t.asciz\t\"" + MF->getName().str() + "\"");
	OutStreamer->EmitRawText("\t.p2align\t4, 0x90");
	OutStreamer->EmitRawText(getNextFunctionMagic()+":");
	
	MDNode *md_ret = MF->getFunction()->getMetadata("sgx_return_type");
	MDString *return_type_string = dyn_cast<MDString>(md_ret->getOperand(0).get());
	assert(return_type_string);
	
	int taint_flag = 0;
	if (return_type_string->getString().str().compare("private") == 0)
		taint_flag = 1;
	else
		taint_flag = 0;

	taint_flag *= 2;
	if (getRegisterTaintSignature(X86::RCX, MF) == 1)
		taint_flag += 1;
	taint_flag *= 2;
	if (getRegisterTaintSignature(X86::RDX, MF) == 1)
		taint_flag += 1;
	taint_flag *= 2;
	if (getRegisterTaintSignature(X86::R8, MF) == 1)
		taint_flag += 1;
	taint_flag *= 2;
	if (getRegisterTaintSignature(X86::R9, MF) == 1)
		taint_flag += 1;
	OutStreamer->EmitRawText("\t.space\t8, 0x9a");
	taint_flag ^= 0b1111;
	OutStreamer->EmitRawText("\t.byte\t" + std::to_string(taint_flag));
	OutStreamer->EmitRawText("\t.space\t7, 0x00");
	
	AsmPrinter::EmitFunctionEntryLabel();

	std::string fname = MF->getName().str();
#ifdef PROFILE_LOG
	OutStreamer->EmitRawText("\tmovq\t%rdx, %r11");
	OutStreamer->EmitRawText("\trdtsc");
	OutStreamer->EmitRawText("\tmovabsq\t$__profiler_data_" + fname+", %r10");
	OutStreamer->EmitRawText("\tmovl\t%eax, 8(%r10)");
	OutStreamer->EmitRawText("\tmovl\t%edx, 12(%r10)");
	OutStreamer->EmitRawText("\tmovq\t%r11, %rdx");
#endif

#ifdef CALLEE_SAVE_CMPSTACK

	OutStreamer->EmitRawText(INS("shadow_stack_enter_callee_save"));
	shadow_stack_push_count = 1;

#endif


	//OutStreamer->EmitRawText("\tshadow_stack_enter");
/*
	
	OutStreamer->EmitRawText("\tmovabsq\t$0x900000150, %r11");
	OutStreamer->EmitRawText("\tmovq\t(%r11), %r10");
	OutStreamer->EmitRawText("\tmovq\t8(%r11), %r11");
	OutStreamer->EmitRawText("\tmovq\t%r10, (%r11)");
	OutStreamer->EmitRawText("\tmovabsq\t$0x900000150, %r11");
	OutStreamer->EmitRawText("\tmovabsq\t$" + fname + ", %r10");
	OutStreamer->EmitRawText("\tmovq\t%r10, (%r11)");
	OutStreamer->EmitRawText("\taddq\t$8, 8(%r11)");
*/
	/*
	OutStreamer->EmitRawText("\tmovq\t%gs:0x100, %r10");
	
	int i;
	OutStreamer->EmitRawText("\tmovb\t$43, (%r10)");
	int len = fname.length();
	//errs() << "len of " << fname << " = " << len << "\n";
	for (i = 0; i < len; i++) {
		OutStreamer->EmitRawText("\tmovb\t$" + std::to_string((int)fname[i]) + ", " + std::to_string(i+1) + "(%r10)");
	}
	OutStreamer->EmitRawText("\tmovb\t$0, " + std::to_string(i+1) + "(%r10)");


	OutStreamer->EmitRawText("\tmovq\t%rdx, %r11");
	OutStreamer->EmitRawText("\trdtsc");
	OutStreamer->EmitRawText("\tmovl\t%eax, " + std::to_string(i + 2) + "(%r10)");
	OutStreamer->EmitRawText("\tmovl\t%edx, " + std::to_string(i + 6) + "(%r10)");
	OutStreamer->EmitRawText("\tmovq\t%r11, %rdx");

	OutStreamer->EmitRawText("\taddq\t$" + std::to_string(i + 10) + ", %gs:0x100");
	*/

	profiler_function_labels.push_back(fname);
}
//===----------------------------------------------------------------------===//
// Target Registry Stuff
//===----------------------------------------------------------------------===//

// Force static initialization.
extern "C" void LLVMInitializeX86AsmPrinter() {
  RegisterAsmPrinter<X86AsmPrinter> X(TheX86_32Target);
  RegisterAsmPrinter<X86AsmPrinter> Y(TheX86_64Target);
}
