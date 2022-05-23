# Build shared lib
add_llvm_library(LLVMSoftBoundCETSLTO MODULE BUILDTREE_ONLY
  SoftBoundCETS.cpp
  FixByValAttributes.cpp
  Utils.cpp

  DEPENDS
  intrinsics_gen

  PLUGIN_TOOL
  opt
)

target_compile_definitions(LLVMSoftBoundCETSLTO PRIVATE SOFTBOUNDCETS_EP_LTO)

add_llvm_library(LLVMSoftBoundCETS MODULE BUILDTREE_ONLY
  SoftBoundCETS.cpp
  FixByValAttributes.cpp
  Utils.cpp

  DEPENDS
  intrinsics_gen

  PLUGIN_TOOL
  opt
)

target_compile_definitions(LLVMSoftBoundCETS PRIVATE SOFTBOUNDCETS_EP_OPT_LAST)

