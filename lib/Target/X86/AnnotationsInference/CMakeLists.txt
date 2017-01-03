SET(Z3_API_PATH "" CACHE PATH "Location of the Z3 api header files")
SET(Z3_LIB_PATH "" CACHE PATH "Location of the Z3 lib files")



include_directories(
	${Z3_API_PATH}
	${LLVM_MAIN_INCLUDE_DIR}/../lib/Target/X86
)

add_llvm_library(LLVMAnnotationsInference 
	AnnotationsInference.cpp
       	Custom.cpp
	MIRRegisterInference.cpp
	SgxMCPasses.cpp
	${Z3_API_HEADERS}	
	ADDITIONAL_HEADER_DIRS
  	${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
	${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/AnnotationsInference
	${LLVM_MAIN_INCLUDE_DIR}/../lib/Target/X86
	
)
target_link_libraries(LLVMAnnotationsInference ${Z3_LIB_PATH}/libz3.lib)
add_dependencies(LLVMAnnotationsInference intrinsics_gen)

