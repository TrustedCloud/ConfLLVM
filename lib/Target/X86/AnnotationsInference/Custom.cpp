#include "llvm/InitializePasses.h"
#include "llvm-c/Initialization.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"


using namespace llvm;

void llvm::initializeAnnotationsInference(PassRegistry &Registry){
	initializeAnnotationsInferencePass(Registry);
}

void LLVMInitializeAnnotationsInference(LLVMPassRegistryRef R){
	initializeAnnotationsInference(*unwrap(R));
}
