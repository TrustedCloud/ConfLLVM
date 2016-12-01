#ifndef LLVM_ANNOTATIONS_INFERENCE_H
#define LLVM_ANNOTATIONS_INFERENCE_H

#include "llvm/CodeGen/MachineInstr.h"
#include<set>

namespace llvm {
	FunctionPass *createAnnotationsInferencePass();
	int inferMIRRegisterType(const MachineInstr*, unsigned, std::set<std::pair<const MachineInstr*, unsigned int>> accessed_mirs);
}


#endif
