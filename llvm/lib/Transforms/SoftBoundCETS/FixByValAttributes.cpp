///=== FixByValAttributes.cpp --*- C++ -*=====///
// Copyright (c) 2016 Santosh Nagarakatte. All rights reserved.

// Developed by: Santosh Nagarakatte, Rutgers University
//               http://www.cs.rutgers.edu/~santosh.nagarakatte/softbound/

// The  SoftBoundCETS project had contributions from:
// Santosh Nagarakatte, Rutgers University,
// Milo M K Martin, University of Pennsylvania,
// Steve Zdancewic, University of Pennsylvania,
// Jianzhou Zhao, University of Pennsylvania

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal with the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

//   1. Redistributions of source code must retain the above copyright notice,
//      this list of conditions and the following disclaimers.

//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimers in the
//      documentation and/or other materials provided with the distribution.

//   3. Neither the names of its developers nor the names of its
//      contributors may be used to endorse or promote products
//      derived from this software without specific prior written
//      permission.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
// CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// WITH THE SOFTWARE.
//===---------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <algorithm>
#include <cstdarg>
#include <set>

#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Pass.h"

#include "llvm-c/Target.h"
#include "llvm-c/TargetMachine.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "FixByValAttributes.h"

#include <queue>

using namespace llvm;

// static cl::opt<bool> fix_all_byval("fix_all_byval",
//                                    cl::desc("Transform all byval
//                                    attributes"), cl::init(true));

// static cl::opt<bool>
//     fix_specific_byval("fix_specific_byval",
//                        cl::desc("Transform only pointer byval attributes"),
//                        cl::init(false));

char FixByValAttributesPass::ID;

bool FixByValAttributesPass::runOnModule(Module &M) {

  bool Change = true;

  while (Change) {
    Change = false;
    for (auto &Fn : M.functions()) {
      if (Fn.getName().contains("fopencookie")) // ignore wrappers
        continue;
      Change = transformFunction(Fn);
      // evaluate if restart of loop when a function has been transformed is
      // warranted -> no
      // restart anew to avoid incorrect pointers as we change the function list
      // while we iterate through it
      if (Change) {
        LLVM_DEBUG(dbgs() << "FixByValAttributes transformed function: "
                          << Fn.getName() << "\n");
        break;
      }
    }
  }

  return true;
}

// copy OldCallSiteArg Pointee to NewCallSiteAlloca (NewCallSiteAlloca is
// replacement in function call)
// do this in a recursive way:
// build indices for GEP and pass them to recursive createGEPStores calls
// first call should be with Indices = [ConstantInt(0)]
void FixByValAttributesPass::createGEPStores(Value *NewCallSiteAlloca,
                                             Value *OldCallSiteArg,
                                             StructType *StructTy,
                                             Instruction *InsertBefore,
                                             std::vector<Value *> Indices) {

  int Idx = 0;

  // iterate over all struct members
  for (auto I = StructTy->element_begin(), E = StructTy->element_end(); I != E;
       ++I, Idx++) {

    std::vector<Value *> NewIndices;
    Type *ElTy = *I;

    for (auto const &OldIdx : Indices) {
      NewIndices.push_back(OldIdx);
    }

    Constant *LoopIdx = ConstantInt::get(
        Type::getInt32Ty(NewCallSiteAlloca->getType()->getContext()), Idx,
        false);
    NewIndices.push_back(LoopIdx);

    if (isa<StructType>(ElTy)) {
      StructType *ElStructTy = dyn_cast<StructType>(ElTy);
      createGEPStores(NewCallSiteAlloca, OldCallSiteArg, ElStructTy,
                      InsertBefore, NewIndices);
    } else {

     GetElementPtrInst *SrcGEP = GetElementPtrInst::Create(
          nullptr, OldCallSiteArg, NewIndices, "", InsertBefore);

      GetElementPtrInst *DestGEP = GetElementPtrInst::Create(
          nullptr, NewCallSiteAlloca, NewIndices, "", InsertBefore);

     LoadInst *Load = new LoadInst(SrcGEP->getType()->getContainedType(0),
                                    SrcGEP, "", InsertBefore);
      auto *DestGEPCast = new BitCastInst(DestGEP, SrcGEP->getType(), "", InsertBefore);
      new StoreInst(Load, DestGEPCast, false, InsertBefore);
    }
  }
}

bool FixByValAttributesPass::transformFunction(Function &F) {

  // for each function:
  // step 1: change function signature by removing all byval attributes for
  // those function arguments which have it
  // step 2: change all affected function calls by
  // - allocating a new object on the stack before the fn call
  // - copying the original function arg which had a byval attribute to this
  // object and
  //- passing a pointer to this new object to the called function (instead of
  // the old byval arg)

  bool FnHasByValArg = false;
  for (auto &FnArg : F.args()) {

    if (FnArg.hasByValAttr()) {
      FnHasByValArg = true;
    }
  }
  if (!FnHasByValArg)
    return false;

  // with an empty VMap we keep all arguments
  ValueToValueMapTy VMap;
  auto *ClonedFunc = CloneFunction(&F, VMap);
  unsigned ArgIdx = 0;

  for (auto &FnArg : ClonedFunc->args()) {
    if (FnArg.hasByValAttr()) {
      ClonedFunc->removeParamAttr(ArgIdx, Attribute::ByVal);
    }
    ArgIdx++;
  }
  replaceFunctionCallsWithByValParams(F, *ClonedFunc);

  F.eraseFromParent();
  return true;
}

/// Goes over OldF calls and replaces them with a call to NewF
/// by replacing byval arguments with allocas
void FixByValAttributesPass::replaceFunctionCallsWithByValParams(
    Function &OldFn, Function &NewFn) {

  std::set <CallBase*> AllUsers;

  for (User *U : OldFn.users()) {
    if (auto *CB = dyn_cast<CallBase>(U)) {
      AllUsers.insert(CB);
    }
    else {
      for (auto *U2 : U->users()){
        if (auto *CB = dyn_cast<CallBase>(U2)) {
          AllUsers.insert(CB);
        }
        else{
          assert(0 && "User not a direct or indirect callbase!");
        }
      }
    }
  }

  for (CallBase *CB : AllUsers) {

      SmallVector<Value *, 8> NewArgs;

      // iterate over function arguments and over CallSite arguments
      auto *CallSiteArg = CB->arg_begin();
      for (auto FnArg = OldFn.arg_begin(), FnArgEnd = OldFn.arg_end();
           FnArg != FnArgEnd; ++FnArg, ++CallSiteArg) {

        if (FnArg->hasByValAttr()) {

          Type *ArgTy = getContainedByValType(FnArg);

          AllocaInst *ByValAlloca;
          StructType *StructTy;

          if ((StructTy = dyn_cast<StructType>(ArgTy))) {
            ByValAlloca = new AllocaInst(StructTy, 0, "", CB);
          } else if (Type *ElTy = GetElementPtrInst::getTypeAtIndex(
                         ArgTy, (uint64_t)0)) {
            StructTy = dyn_cast<StructType>(ElTy);
            assert(StructTy && "non-struct byval parameters?");
            ByValAlloca = new AllocaInst(StructTy, 0, "", CB);

          } else {
            assert(0 && "byval parameter not yet handled!");
          }

          std::vector<Value *> Indices;
          Constant *StartIdx = ConstantInt::get(
              Type::getInt64Ty(ByValAlloca->getType()->getContext()), 0, false);
          Indices.push_back(StartIdx);

          createGEPStores(ByValAlloca, *CallSiteArg, StructTy, CB, Indices);
          NewArgs.push_back(ByValAlloca);

        } else {
          NewArgs.push_back(*CallSiteArg);
        }
      }
      // new functioncall: with pointer to alloca instead of original pointer
      CallBase *NewCB;

      if (auto *CI = dyn_cast<CallInst>(CB)) {
        NewCB = CallInst::Create(&NewFn, NewArgs);
      } else if (auto *II = dyn_cast<InvokeInst>(CB)) {
        NewCB = InvokeInst::Create(&NewFn, II->getNormalDest(),
                                   II->getUnwindDest(), NewArgs);
      } else {
        assert(0 && "Function User not handled!");
      }

      NewCB->setCallingConv(NewFn.getCallingConv());
      if (!CB->use_empty())
        CB->replaceAllUsesWith(NewCB);
      ReplaceInstWithInst(CB, NewCB);
 }
}
