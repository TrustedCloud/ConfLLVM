list(APPEND LLVM_COMMON_DEPENDS intrinsics_gen)
#set(LLVM_LINK_COMPONENTS
    #    ${LLVM_TARGETS_TO_BUILD}
    #  AnnotationsInference
    #)

add_llvm_library(LLVMTarget
  Target.cpp
  TargetIntrinsicInfo.cpp
  TargetLoweringObjectFile.cpp
  TargetMachine.cpp
  TargetMachineC.cpp
  TargetRecip.cpp
  TargetSubtargetInfo.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Target
  )


foreach(t ${LLVM_TARGETS_TO_BUILD})
  message(STATUS "Targeting ${t}")
  add_subdirectory(${t})
endforeach()
