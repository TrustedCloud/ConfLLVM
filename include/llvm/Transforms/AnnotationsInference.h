#ifndef LLVM_ANNOTATIONS_INFERENCE_H
#define LLVM_ANNOTATIONS_INFERENCE_H

#include "llvm/CodeGen/MachineInstr.h"


namespace llvm {
	FunctionPass *createAnnotationsInferencePass();
	int inferMIRRegisterType(MachineInstr*, unsigned);
}


#endif
