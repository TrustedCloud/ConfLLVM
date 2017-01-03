#ifndef LLVM_ANNOTATIONS_INFERENCE_H
#define LLVM_ANNOTATIONS_INFERENCE_H

#include "llvm/CodeGen/MachineInstr.h"
#include<set>

namespace llvm {
	FunctionPass *createAnnotationsInferencePass();
	typedef std::set<unsigned> register_set;
	typedef std::map<const MachineBasicBlock*, register_set> register_set_map;
	
	register_set processMachineBasicBlockForTaint(const MachineBasicBlock *MBB, register_set temp_set, const MachineInstr *OMI, int OReg, int &return_taint);
	register_set_map processMachineFunctionForTaint(const MachineFunction* MF, const MachineInstr *OMI, int OReg, int &return_taint);

	//int inferMIRRegisterType(const MachineInstr*, unsigned, std::set<std::pair<const MachineInstr*, unsigned int>> accessed_mirs);
	int inferTaintForSpilling(const MachineInstr *OMI, unsigned OReg);
	int inferTaintForCodeGen(const MachineInstr *OMI, unsigned OReg, register_set private_set);
}


#endif
