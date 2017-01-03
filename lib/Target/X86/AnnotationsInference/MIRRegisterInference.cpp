#include "llvm/Transforms/AnnotationsInference.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include <set>

#include "X86RegisterInfo.h"
#include "X86ShuffleDecodeConstantPool.h"
#include "InstPrinter/X86ATTInstPrinter.h"
#include "MCTargetDesc/X86BaseInfo.h"
#include "Utils/X86ShuffleDecode.h"

#ifdef DO_INFER_DEBUG
#define INFER_DEBUG(x) x
#else
#define INFER_DEBUG(x)
#endif

namespace llvm {

	

	bool insertSet(register_set &to, register_set from) {
		int orig_length = to.size();
		for (auto register_iterator = from.begin(); register_iterator != from.end(); register_iterator++) {
			to.insert(*register_iterator);
		}
		if (orig_length != to.size()) {
			return true;
		}
		return false;
	}

	int inferTaintForInstruction(const MachineInstr* MI, register_set private_set) {
		if (MI->getFlags() & MachineInstr::FrameDestroy)
			return 0;
		if (MI->register_sgx_type != 0)
			return MI->register_sgx_type;
		if (MI->mayLoad() && MI->sgx_type == 0) {
			MI->dump();
			llvm_unreachable("All loads must have a type!");
		}
		if (MI->isCall()) {
			llvm_unreachable("This shouldn't happen (Call without register_sgx_type)!");
		}

		/* Special cases*/
		if (MI->getOpcode() == X86::XOR16rr || MI->getOpcode() == X86::XOR32rr || MI->getOpcode() == X86::XOR64rr || MI->getOpcode() == X86::XOR8rr) {
			if (MI->uses().begin()->getReg() == (MI->uses().begin() + 1)->getReg())
				return 2;
		}
		/*Special cases*/
		
		if (MI->mayLoad() && MI->sgx_type == 1)
			return 1;
		for (auto OP = MI->uses().begin(); OP != MI->uses().end(); OP++) {
			if (OP->isReg() && OP->getReg() != X86::EFLAGS && OP->getReg() != X86::RSP && OP->getReg() != X86::NoRegister) {
				if (private_set.find(OP->getReg()) != private_set.end()) {
					return 1;
				}
			}
		}
		return 2;
	}

	bool checkRegisterEqual(const TargetRegisterInfo *TRI, unsigned Reg1, unsigned Reg2) {
		if (!TRI->isPhysicalRegister(Reg1) || !TRI->isPhysicalRegister(Reg2)) {
			return Reg1 == Reg2;
		}
		else {
			return TRI->isSuperOrSubRegisterEq(Reg1, Reg2);
		}
	}

	register_set processMachineBasicBlockForTaint(const MachineBasicBlock *MBB, register_set temp_set, const MachineInstr *OMI, int OReg, int &return_taint) {
		const TargetRegisterInfo *TRI = MBB->getParent()->getSubtarget().getRegisterInfo();

		for (auto MI = MBB->begin(); MI != MBB->end(); MI++) {
			INFER_DEBUG(errs() << "Analyzing ";
			MI->dump();)
			bool isDef = false;
			unsigned defReg = 0;
			int defCounter = 0;
			for (auto OP = MI->operands_begin(); OP != MI->operands_end(); OP++) {
				if (OP->isReg() && OP->isDef()) {
					int Reg = OP->getReg();
					if (Reg != X86::RSP && Reg != X86::EFLAGS && Reg != X86::NoRegister) {
						isDef = true;
						if (checkRegisterEqual(TRI, Reg, defReg))
							defCounter++;
						defReg = Reg;

					}
				}
			}
			if (defCounter > 1) {
				MI->dump();
				llvm_unreachable("More than one def on MCInstr");
			}
			if (isDef) {
				int taint = inferTaintForInstruction(MI.getInstrIterator().getNodePtrUnchecked(), temp_set);
				if (taint == 1) {
					if (!TRI->isPhysicalRegister(defReg))
						temp_set.insert(defReg);
					else
						for (MCRegAliasIterator alias(defReg, TRI, true); alias.isValid(); ++alias)
							temp_set.insert(*alias);
				}
				else {
					if (!TRI->isPhysicalRegister(defReg))
						temp_set.erase(defReg);
					else
						for (MCRegAliasIterator alias(defReg, TRI, true); alias.isValid(); ++alias)
							temp_set.erase(*alias);
				}
			}
			if (OMI == MI.getInstrIterator().getNodePtrUnchecked()) {
				if (temp_set.find(OReg) == temp_set.end()) {
					return_taint = 2;
				}
				else {
					return_taint = 1;
				}
			}
		}
		return temp_set;
	}

	register_set_map processMachineFunctionForTaint(const MachineFunction* MF, const MachineInstr *OMI, int OReg, int &return_taint){
		const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
		register_set_map start_set;
		register_set_map end_set;
		const MachineBasicBlock *entry_block = MF->begin().getNodePtrUnchecked();
		for (auto reg_iterator = MF->live_in_types.begin(); reg_iterator != MF->live_in_types.end(); reg_iterator++) {
			if (reg_iterator->second == 1)
				start_set[entry_block].insert(reg_iterator->first);
		}
		bool repeat = true;
		while (repeat) {
			repeat = false;
			for (auto MBB = MF->begin(); MBB != MF->end(); MBB++) {
				INFER_DEBUG(errs() << "Starting BB " << MBB->getName().str() << "\n";)
					for (auto pMBB = MBB->pred_begin(); pMBB != MBB->pred_end(); pMBB++) {
						insertSet(start_set[MBB.getNodePtrUnchecked()], end_set[*pMBB]);
					}
				register_set temp_set;
				temp_set = start_set[MBB.getNodePtrUnchecked()];
				temp_set = processMachineBasicBlockForTaint(MBB.getNodePtrUnchecked(), temp_set, OMI, OReg, return_taint);
				if (insertSet(end_set[MBB.getNodePtrUnchecked()], temp_set))
					repeat = true;
				INFER_DEBUG(errs() << "Ending BB " << MBB->getName().str() << "\n";)
			}
		}
		return start_set;
	}

	int inferTaintForSpilling(const MachineInstr *OMI, unsigned OReg) {
		INFER_DEBUG(errs() << "Entering infer for spill\n";)
		int final_taint = 0;
		const MachineFunction *MF = OMI->getParent()->getParent();
		
		processMachineFunctionForTaint(MF, OMI, OReg, final_taint);

		if (final_taint == 0) {
			llvm_unreachable("Taint info not found for given MI, Reg pair\n");
		}
		INFER_DEBUG(errs() << "Leaving infer for spill\n";)
		return final_taint;
		
	}

	int inferTaintForCodeGen(const MachineInstr *OMI, unsigned OReg, register_set private_set) {
		INFER_DEBUG(errs() << "Entering infer for code gen\n";)
		int final_taint = -1;
		
		const MachineBasicBlock *MBB = OMI->getParent();
		processMachineBasicBlockForTaint(MBB, private_set, OMI, OReg, final_taint);
		if (final_taint == 0) {
			llvm_unreachable("Taint info not found for given MI, Reg pair\n");
		}

		INFER_DEBUG(errs() << "Leaving infer for code gen\n";)
		return final_taint;
	}

}
