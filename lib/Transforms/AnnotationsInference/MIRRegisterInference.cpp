#include "llvm/Transforms/AnnotationsInference.h"
#include "llvm/CodeGen/MachineBasicBlock.h"

namespace llvm {

	int sgx_type_intersect(int a, int b) {
		if (a == 0 || b == 0)
			llvm_unreachable("Can't intersect sgx_undef");
		if (a == 2 || b == 2)
			return 2;
		else
			return 1;
	}

	int inferMIRRegisterType(MachineInstr *MI, unsigned Reg) {
		//errs() << "entering infer with ";
		//MI->dump();
		//errs() << " " << Reg << "\n";
		MachineInstr *PM = MI;
		while (PM) {
			//PM->dump();
			llvm::iterator_range<MachineOperand*> operands = PM->operands();
			bool isDef = false;
			for (MachineOperand *Oi = operands.begin(); Oi != operands.end(); Oi++) {
				if (Oi->isReg() && Oi->isDef() && Oi->getReg() == Reg) {
					isDef = true;
					break;
				}	
			}
			if (isDef) {
				
				if (PM->register_sgx_type)
					return PM->register_sgx_type;
				if (PM->mayLoad() && PM->sgx_type != 0) {
					PM->register_sgx_type = PM->sgx_type;
			//		errs() << "SETTING LOAD TYPE FOR :";
			//		PM->dump();
					return PM->sgx_type;
				}
				if (PM->mayLoad() && PM->sgx_type == 0) {
					llvm_unreachable("All loads must have a type");
				}
				if (PM->isCall()) {
					PM->register_sgx_type = 2;
				//	errs() << "SETTING CALL TYPE FOR :";
					PM->dump();
					return 2;
				}
				int sgx_type = 2;
				for (MachineOperand *Oi = PM->uses().begin(); Oi != PM->uses().end(); Oi++) {
					if (Oi->isReg()) {
						int o_type = inferMIRRegisterType(PM->getPrevNode(), Oi->getReg());
						sgx_type = sgx_type_intersect(sgx_type, o_type);
					}
				}	
				PM->register_sgx_type = sgx_type;
				//errs() << "SETTING FINAL TYPE FOR :";
				//PM->dump();
				return sgx_type;
			}
			else {
				//errs() << "Skipping\n";
			}
			PM = PM->getPrevNode();
		}
		MachineBasicBlock *BB = MI->getParent();
		if (BB->pred_begin() == BB->pred_end())
			return 2;
		else {
			int sgx_type = 0;
			for (MachineBasicBlock::pred_iterator pBB = BB->pred_begin(); pBB != BB->pred_end(); pBB++) {
				MachineBasicBlock::instr_iterator last = (*pBB)->instr_end();
				last--;
				int o_type = inferMIRRegisterType(last.getNodePtrUnchecked(), Reg);
				if (sgx_type == 0)
					sgx_type = o_type;
				else if (sgx_type != o_type) {
					llvm_unreachable("Inferred different types from two branches for same register!");
				}
			}
		}
		return 2;
	}
}
