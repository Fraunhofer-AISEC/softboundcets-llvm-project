#include "llvm/Transforms/Instrumentation.h"
#include "llvm-c/Target.h"
#include "llvm-c/TargetMachine.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_ostream.h"


#include <algorithm>
#include <cstdarg>
#include <queue>

#include "Utils.h"

using namespace llvm;

#define DEBUG_TYPE "softboundcets"

/// Why do we need to fix arguments with a byval attribute?
/// byval Attribute: https://llvm.org/docs/LangRef.html#parameter-attributes
/// Why byval: https://lists.llvm.org/pipermail/llvm-dev/2018-April/122714.html 

/// byval is treated/lowered in the backend, but SoftBoundCETS needs to pass its metadata also to functions receiving a byval pointer
/// Solution: iterate over all functions, remove byval attributes and make copy of passed object on the stack before the function call

// NOTE: As of now, this pass does only work when running in LTO.
// If we run it in OptimizerLast, we do not change function calls in other modules.
// This leads to a linking error function references to the original functions cannot be resolved.
// Possible solution: iterate in each Module over CallInst/Invoke where Arg with pointers is passed ByVal
// Change these calls as we do it now: allocas before function call and associate metadata  
class FixByValAttributesPass: public ModulePass{

 private:
  bool runOnModule(Module &) override;
  bool transformFunction(Function&);
  bool checkPtrsInST(StructType*);
  void replaceFunctionCallsWithByValParams(Function &OldF, Function &NewF);
  void createGEPStores(Value*, Value*,StructType*, Instruction*, 
                       std::vector<Value*>);

 public:
  static char ID;
 FixByValAttributesPass(): ModulePass(ID){
  }

  llvm::StringRef getPassName() const override { return "FixByValAttributes";}
};

