#include "llvm/IR/Argument.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include <map>
#include <set>

using namespace llvm;

#define DEBUG_TYPE "softboundcets"

bool isTypeWithPointers(Type *Ty);
size_t countPointersInType(Type *Ty);
bool isVectorWithPointers(Type *Ty);
size_t countMetadata(Type *Ty);

// get Type byval pointer points to (as byval arg usually(always?) is a pointer
// to another type)
Type *getContainedByValType(Argument *FnArg);
void collectVarargPointerLoads(Instruction *Root, SmallVector<LoadInst *> &LoadInsts,
                               std::set<Value *> &Visited);
