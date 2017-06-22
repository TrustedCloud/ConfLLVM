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
using namespace llvm;

namespace {
	class MachineInstPrint : public MachineFunctionPass {
	public:
		static char ID;
		MachineInstPrint() : MachineFunctionPass(ID) {}
		/*bool runOnMachineFunction(MachineFunction &MF) {
			return false;
		}*/
		bool runOnMachineFunction(MachineFunction &MF) {
			for (MachineFunction::iterator MBBi = MF.begin(); MBBi != MF.end(); MBBi++) {
				MachineBasicBlock &MBB = *MBBi;
				for (MachineBasicBlock::iterator MIi = MBB.begin(); MIi != MBB.end(); MIi++) {
					MachineInstr &MI = *MIi;
					for (int i = 0; i < MI.getNumOperands();i++) {
						MachineOperand &MO = MI.getOperand(i);
						if (MO.isMetadata()) {
							const MDNode *mdn = MO.getMetadata();
							mdn->dump();
							errs() << MI << "\n";
						}
					}
				}
			}
			return false;
		}
	};
	char MachineInstPrint::ID = 0;
}

FunctionPass *llvm::createMachineInstPrint() {
	return new MachineInstPrint();
}
