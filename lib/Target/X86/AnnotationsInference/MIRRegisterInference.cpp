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
namespace llvm {

	int sgx_type_intersect(int a, int b) {
		if (a == -1 || b == -1)
			return -1;
		if (a == 0 || b == 0)
			llvm_unreachable("Can't intersect sgx_undef");
		if (a == 1 || b == 1)
			return 1;
		else
			return 2;
	}
	int getRegisterTypeFromPrevBB(const MachineInstr *MI, unsigned Reg, std::set<std::pair<const MachineInstr*, unsigned int>> accessed_mirs) {
		const MachineBasicBlock *BB = MI->getParent();
		if (BB->pred_begin() == BB->pred_end()) {
			const MachineFunction *MF = BB->getParent();
			const TargetMachine &TM = MF->getTarget();
			const MCRegisterInfo *MRI = TM.getMCRegisterInfo();
			//TODO check sub reg instead of just reg


			int act_reg = -1;
			for (auto reg_iterator = MF->live_in_types.begin(); reg_iterator != MF->live_in_types.end(); reg_iterator++) {
				if (MRI->isSuperOrSubRegisterEq(reg_iterator->first, Reg))
					act_reg = reg_iterator->first;
			}

			if (act_reg!=-1) {
				return MF->live_in_types.find(act_reg)->second;
			}

			//llvm_unreachable("Hit top with MIR RegisterInference and not in live ins!");
			return -1;
		}
		else {
			int sgx_type = 0;
			for (MachineBasicBlock::const_pred_iterator pBB = BB->pred_begin(); pBB != BB->pred_end(); pBB++) {
				MachineBasicBlock::instr_iterator last = (*pBB)->instr_end();
				//errs() << "Going to parent branch\n";
				last--;
				int o_type = inferMIRRegisterType(last.getNodePtrUnchecked(), Reg, accessed_mirs);
				//errs() << "prev block res " << Reg << " - " << o_type << "\n";
				if (o_type == -1)
					return -1;
				if (sgx_type == 0)
					sgx_type = o_type;
				else if (sgx_type != o_type) {
					llvm::errs() << "sgx_type = " << sgx_type << " o_type = " << o_type << "\n";
					llvm_unreachable("Inferred different types from two branches for same register!");
				}
			}
			return sgx_type;
		}
	}

	int inferMIRRegisterType(const MachineInstr *MI, unsigned Reg, std::set<std::pair<const MachineInstr*, unsigned int>> accessed_mirs) {
		if (Reg == X86::RSP || Reg == X86::NoRegister)
			return 2;
		//errs() << "entering infer with \n";
		//MI->dump();
		//errs() << " " << Reg << "\n";
		const MachineInstr *PM = MI;
		while (PM) {
			//PM->dump();
			if (accessed_mirs.find(std::pair<const MachineInstr*, unsigned>(PM, Reg)) != accessed_mirs.end()) {
				return 2;
			}
			accessed_mirs.insert(std::pair<const MachineInstr*, unsigned>(PM, Reg));
			llvm::iterator_range<const MachineOperand*> operands = PM->operands();
			bool isDef = false;
			const MachineBasicBlock *BB = MI->getParent();
			const MachineFunction *MF = BB->getParent();
			const TargetMachine &TM = MF->getTarget();
			const MCRegisterInfo *MRI = TM.getMCRegisterInfo();
			for (const MachineOperand *Oi = operands.begin(); Oi != operands.end(); Oi++) {
				if (Oi->isReg() && Oi->isDef() && MRI->isSuperOrSubRegisterEq(Oi->getReg(),Reg)) {
					isDef = true;
					break;
				}	
			}
			if (isDef) {
				//PM->dump();
				//errs() << "is a def\n";
				if (PM->register_sgx_type) {
					//errs() << "returning - " << PM->register_sgx_type<<"\n";
					return PM->register_sgx_type;
				}
					
				if (PM->mayLoad() && PM->sgx_type != 0) {
					//PM->register_sgx_type = PM->sgx_type;
			//		errs() << "SETTING LOAD TYPE FOR :";
			//		PM->dump();

					//TODO include it to add taints of other regs too
					return PM->sgx_type;
				}
				if (PM->mayLoad() && PM->sgx_type == 0) {
					llvm_unreachable("All loads must have a type");
				}
				if (PM->isCall()) {
					//PM->register_sgx_type = 2;
					llvm_unreachable("SETTING CALL TYPE FOR(this shouldn't be happening!) :");
					PM->dump();
					return 2;
				}
				if (PM->getOpcode() == X86::XOR16rr || PM->getOpcode() == X86::XOR32rr || PM->getOpcode() == X86::XOR64rr) {
					if (PM->uses().begin()->getReg() == (PM->uses().begin() + 1)->getReg()) {
						errs() << "XOR optimization!\n";
						PM->dump();
						return 2;
					}
						
				}
				int sgx_type = 2;
				//int counter = 0;
				for (const MachineOperand *Oi = PM->uses().begin(); Oi != PM->uses().end(); Oi++) {
					//PM->dump();
					//errs() << "Arg number " << counter << "\n";
					
					if (Oi->isReg() && Oi->getReg() != X86::EFLAGS) {
						int o_type;
						if(PM->getPrevNode())
							o_type = inferMIRRegisterType(PM->getPrevNode(), Oi->getReg(), accessed_mirs);
						else
							o_type = getRegisterTypeFromPrevBB(PM, Oi->getReg(), accessed_mirs);
						//errs() << "got o_type = " << o_type << "\n";
						sgx_type = sgx_type_intersect(sgx_type, o_type);
					}
					//counter++;
				}	
				//PM->register_sgx_type = sgx_type;
				//errs() << "SETTING FINAL TYPE FOR :";
				//PM->dump();
				return sgx_type;
			}
			else {
				//errs() << "Skipping\n";
				//PM->dump();
			}
			PM = PM->getPrevNode();
		}
		return getRegisterTypeFromPrevBB(MI, Reg, accessed_mirs);
		
		llvm_unreachable("MIR RegisterInference cannot reach here!");
		return 2;
	}
}
