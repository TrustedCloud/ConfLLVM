#include "X86.h"
#include "X86FrameLowering.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86MachineFunctionInfo.h"
#include "X86Subtarget.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/Passes.h" // For IDs of passes that are preserved.
#include "llvm/IR/GlobalValue.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
using namespace llvm;

namespace {
	class SgxMCPasses : public MachineFunctionPass {
	public:
		static char ID;
		SgxMCPasses() : MachineFunctionPass(ID) {}
		/*bool runOnMachineFunction(MachineFunction &MF) {
			return false;
		}*/

		void removeCall64m(MachineFunction &MF) {
			const TargetInstrInfo *TII;
			const X86Subtarget *STI;
			STI = &MF.getSubtarget<X86Subtarget>();
			TII = STI->getInstrInfo();
			MachineRegisterInfo *MRI = &MF.getRegInfo();
			for (MachineFunction::iterator BBi = MF.begin(); BBi != MF.end(); BBi++) {
				for (MachineBasicBlock::iterator MCi = BBi->begin(); MCi != BBi->end(); MCi++) {
					if (MCi->getOpcode() == X86::CALL64m) {
						//errs() << "Found a call to memory!\n";
						unsigned Reg = MRI->createVirtualRegister(&X86::GR64RegClass);
						MachineBasicBlock::iterator MOV = BuildMI(*BBi, MCi, MCi->getDebugLoc(), TII->get(X86::MOV64rm), Reg).addOperand(MCi->getOperand(0)).addOperand(MCi->getOperand(1)).addOperand(MCi->getOperand(2)).addOperand(MCi->getOperand(3)).addOperand(MCi->getOperand(4));
						MOV->addMemOperand(MF, *MCi->memoperands().begin());
						MOV->sgx_type = MCi->sgx_type;
						MachineBasicBlock::iterator CALL = BuildMI(*BBi, MCi, MCi->getDebugLoc(), TII->get(X86::CALL64r)).addReg(Reg);
						CALL->register_sgx_type = MCi->register_sgx_type;
						CALL->call_arg_taint = MCi->call_arg_taint;
						CALL->isIndirectCall = MCi->isIndirectCall;
						CALL->copyImplicitOps(MF, *MCi);
						BBi->erase(MCi);
						MCi = CALL;
					}
				}
			}
		}

		bool runOnMachineFunction(MachineFunction &MF) {
			removeCall64m(MF);
			return true;
		}
	};
	char SgxMCPasses::ID = 0;
}

FunctionPass *llvm::createSgxMCPass() {
	return new SgxMCPasses();
}