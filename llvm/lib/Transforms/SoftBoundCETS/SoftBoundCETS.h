//=== SoftBound/SoftBoundCETSPass.h - Definitions for the SoftBound/CETS --*-
// C++ -*===//
// Copyright (c) 2014 Santosh Nagarakatte, Milo M. K. Martin. All rights
// reserved.
//
// Developed by: Santosh Nagarakatte,
//               Department of Computer Science,
//               Rutgers University
//               http://www.cs.rutgers.edu/~santosh.nagarakatte/softbound/
//
//               in collaboration with
//               Milo Martin, Jianzhou Zhao, Steve Zdancewic
//               University of Pennsylvania
//
//
//
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

//   3. Neither the names of Santosh Nagarakatte, Milo M. K. Martin,
//      Jianzhou Zhao, Steve Zdancewic, University of Pennsylvania,
//      Rutgers University, nor the names of its contributors may be
//      used to endorse or promote products derived from this Software
//      without specific prior written permission.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
// CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// WITH THE SOFTWARE.

//===---------------------------------------------------------------------===//

#ifndef SOFTBOUNDCETSPASS_H
#define SOFTBOUNDCETSPASS_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cstdarg>

#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

#include "llvm-c/Target.h"
#include "llvm-c/TargetMachine.h"

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/SpecialCaseList.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <queue>

using namespace llvm;

#define DEBUG_TYPE "softboundcets"

typedef IRBuilder<TargetFolder> BuilderTy;

struct SoftBoundCETSMetadata {
  Value *Base;
  Value *Bound;
  Value *Key;
  Value *Lock;
};

class SoftBoundCETSPass : public ModulePass {

private:
  const DataLayout *DL;
  // const TargetLibraryInfo *TLI;
  LLVMContext *C;
  Module *M;
  BuilderTy *Builder;
  SmallString<64> BlacklistFile;
  std::unique_ptr<SpecialCaseList> Blacklist;

  FunctionCallee IntrospectMetadataFn;
  FunctionCallee CopyMetadataFn;
  FunctionCallee AllocateShadowStackFn;
  FunctionCallee DeallocateShadowStackFn;
  FunctionCallee StoreMetadataShadowStackFn;
  FunctionCallee LoadMetadataPtrShadowStackFn;
  FunctionCallee LoadBaseShadowStackFn;
  FunctionCallee LoadBoundShadowStackFn;
  FunctionCallee LoadKeyShadowStackFn;
  FunctionCallee LoadLockShadowStackFn;

  FunctionCallee AllocateStackLockAndKeyFn;
  FunctionCallee DeallocateStackLockAndKeyFn;

  FunctionCallee SpatialLoadDereferenceCheckFn;
  FunctionCallee SpatialStoreDereferenceCheckFn;
  FunctionCallee TemporalLoadDereferenceCheckFn;
  FunctionCallee TemporalStoreDereferenceCheckFn;

  FunctionCallee CallDereferenceCheckFn;
  FunctionCallee MemcpyDereferenceCheckFn;
  FunctionCallee MemsetDereferenceCheckFn;

  FunctionCallee GetGlobalLockFn;
  FunctionCallee StoreMetadataFn;
  FunctionCallee StoreVectorMetadataFn;

  FunctionCallee LoadMetadataPtrFn;
  FunctionCallee LoadMetadataBaseFn;
  FunctionCallee LoadMetadataBoundFn;
  FunctionCallee LoadMetadataLockFn;
  FunctionCallee LoadMetadataKeyFn;

  FunctionCallee LoadVectorMetadataBaseFn;
  FunctionCallee LoadVectorMetadataBoundFn;
  FunctionCallee LoadVectorMetadataLockFn;
  FunctionCallee LoadVectorMetadataKeyFn;
  FunctionCallee LoadVectorMetadataPtrFn;

  FunctionCallee MaskedLoadVectorMetadataBaseFn;
  FunctionCallee MaskedLoadVectorMetadataBoundFn;
  FunctionCallee MaskedLoadVectorMetadataLockFn;
  FunctionCallee MaskedLoadVectorMetadataKeyFn;
  FunctionCallee LoadMaskedVectorMetadataPtrFn;

  /* void pointer type, used many times in the Softboundcets pass */
  PointerType *MVoidPtrTy;
  Type *MSizetTy;
  PointerType *MLockPtrTy;

  /* constant null pointer which is the base and bound for most
   * non-pointers
   */
  ConstantPointerNull *MVoidNullPtr;
  ConstantPointerNull *MSizetNullPtr;
  Type *MKeyTy;
  Type *MArgNoTy;

  Constant *MConstantIntOne;
  Constant *MConstantIntZero;

  Constant *MGlobalLockOne;
  std::set<Constant*> MGlobalLockOnes;

  /* Infinite bound where bound cannot be inferred in VarArg
   * functions
   */
  Constant *MInfiniteBoundPtr;

  /* Dominance Tree and Dominance Frontier for avoiding load
   * dereference checks
   */

  DominatorTree *m_dominator_tree;

  /* Book-keeping structures for identifying original instructions in
   * the program, pointers and their corresponding base and bound
   */
  // std::map<Value*, int> m_is_pointer;
  std::map<Value *, TinyPtrVector<Value *>> MValueBaseMap;
  std::map<Value *, TinyPtrVector<Value *>> MValueBoundMap;

  /* key associated with pointer */
  std::map<Value *, TinyPtrVector<Value *>>
      MValueKeyMap; /* address of the location to load the key from */
  std::map<Value *, TinyPtrVector<Value *>> MValueLockMap;

  std::map<Value *, BasicBlock *> MFaultingBlock;

  std::map<Value *, int> MPresentInOriginal;

  /* Map of all functions for which Softboundcets Transformation must
   * be invoked
   */
  StringMap<bool> m_func_softboundcets_transform;

  /* Map of all functions that need to be transformed as they have as
   * they either hava pointer arguments or pointer return type and are
   * defined in the module
   */
  StringMap<bool> m_func_to_transform;

  /* Map of all functions defined by Softboundcets */
  static StringMap<bool> MFunctionHasSoftboundCETSDefinition;
  static StringSet<> MIgnorableLLVMIntrinsics;

  static StringMap<bool> MFunctionWrappersAvailable;

  /* Map of all functions transformed */
  StringMap<bool> m_func_transformed;

  /* Boolean indicating whether bitcode generated is for 64bit or
     32bit */
  bool m_is_64_bit;

  SmallSet<Function *, 32> InstrumentedFunctions;

  /* Main functions implementing the structure of the Softboundcets
     pass
   */
  bool runOnModule(Module &) override;

  void initializeInitFunctions(Module &M);
  void initializeDereferenceCheckHandlers(Module &M);
  void initializeMetadataHandlers(Module &M);
  void initializeSoftBoundVariables(Module &M);
  void insertGlobalCtor(Module &);
  void identifyOriginalInst(Function *);
  bool isAllocaPresent(Function *);
  void gatherBaseBoundPass1(Function &F);
  void gatherBaseBoundPass2(Function &F);
  void addDereferenceChecks(Function *);
  bool checkIfFunctionOfInterest(Function *);
  bool isFunctionNotToInstrument(const StringRef &str);
  bool isIgnorableLLVMIntrinsic(const StringRef &str);
  bool isExternalDefinitelyInstrumentedFunction(const StringRef &str);
  std::string transformFunctionName(const std::string &str);
  void runForEachFunctionIndirectCallPass(Function &);
  void indirectCallInstPass(Module &);
  bool checkStructTypeWithGEP(BasicBlock *, std::map<Value *, int> &, Value *,
                              BasicBlock::iterator);

  /* Specific LLVM instruction handlers in the bitcode */
  void handleAlloca(AllocaInst *AI, Value *Key, Value *Lock, Value *);

  void insertPointerMetadataLoad(Value *, SoftBoundCETSMetadata &Metadata,
                                 Instruction *InsertAt);

  void insertVectorMetadataLoad(Value *LoadSrc, SoftBoundCETSMetadata &Metadata,
                                Instruction *InsertAt, size_t NumElements);
  void handleLoad(LoadInst *);
  void handleVectorStore(StoreInst *);
  void handleVectorLoad(LoadInst *);

  void handlePointerLoad(LoadInst *Load);
  void handleAggregateLoad(LoadInst *);
  void handleAggregateStore(StoreInst *);
  void handleStore(StoreInst *);
  void handleGEP(GetElementPtrInst *);
  void handleShuffleVector(ShuffleVectorInst *);
  void handleMaskedVectorLoad(CallBase *);

  bool isVaargGep(GetElementPtrInst *);
  void varargAssociatePointerLoads(Instruction *);

  void handleBitCast(BitCastInst *);
  void handlePHIPass1(PHINode *);
  void handlePHIPass2(PHINode *);
  void handleCall(CallBase *);
  void handleMemcpy(CallBase *);
  void handleIndirectCall(CallInst *);
  void handleExtractValue(ExtractValueInst *);
  void handleExtractElement(ExtractElementInst *);
  void handleInsertElement(InsertElementInst *);
  void handleSelect(SelectInst *);
  void handleIntToPtr(IntToPtrInst *);
  void identifyFuncToTrans(Module &);

  void handleInsertValue(InsertValueInst *);

  void transformFunctions(Module &);
  bool transformIndividualFunction(Module &);
  bool hasPtrArgRetType(Function *);
  void iterateOverSuccessors(Function &);
  void transformExternalFunctions(Module &);
  bool transformIndividualExternalFunctions(Module &);
  void transformAndRedirectMain(Module &);
  void renameFunctions(Module &);
  void renameFunctionName(Function *, Module &, bool);
  bool checkAndShrinkBounds(GetElementPtrInst *, Value *);

  // bool isByValDerived(Value*);

  bool checkBitcastShrinksBounds(Instruction *);
  bool isStructOperand(Value *);
  void addSpatialChecks(Instruction *, std::map<Value *, int> &);
  void addTemporalChecks(Instruction *, std::map<Value *, int> &,
                         std::map<Value *, int> &);

  bool optimizeTemporalChecks(Instruction *, std::map<Value *, int> &,
                              std::map<Value *, int> &);

  bool bbTemporalCheckElimination(Instruction *, std::map<Value *, int> &);

  bool funcTemporalCheckElimination(Instruction *, std::map<Value *, int> &);

  bool optimizeConstsGlobalAndStackVariableChecks(Instruction *);
  bool checkLoadStoreSourceIsGEP(Instruction *, Value *);
  void addMemcopyMemsetCheck(CallBase *, Function *);
  bool isMemcopyFunction(Function *);

  void getFunctionKeyLock(Function *, Value *&, Value *&, Value *&);
  void freeFunctionKeyLock(Function *, Value *&, Value *&, Value *&);
  Value *getPointerLoadStore(Instruction *);
  void propagateMetadata(Value *, Instruction *);

  void getFunctionKeyLock(Function &, Value *&, Value *&, Value *&);
  void addMemoryAllocationCall(Function *, Value *&, Value *&, Instruction *);

  enum { SBCETS_BITCAST, SBCETS_GEP };
  /* Auxillary base and propagation functions */

  void addMetadataToGlobals(Module &);
  void addMetadataToGlobal(GlobalVariable &);
  size_t flattenAggregateIndices(Type *, ArrayRef<unsigned>);
  void generateAggregateGEPs(Value *pointer, Type *pointee_type,
                             Instruction *insert_at,
                             SmallVector<Value *, 8> &gep);

  template <typename T> TinyPtrVector<T *> createConstantBases(Constant *Const);
  template <typename T>
  TinyPtrVector<T *> createConstantBounds(Constant *Const,
                                          bool IsGlobal = false);
  template <typename T>
  TinyPtrVector<T *> createConstantKeys(Constant *Const, bool IsGlobal = false);
  void getConstantExprBaseBoundArray(Constant *constant,
                                     TinyPtrVector<Value *> &base_array,
                                     TinyPtrVector<Value *> &bound_array);

  Instruction *getGlobalsInitializerInsertPoint(Module &);
  void dissociateBaseBound(Value *);
  void dissociateKeyLock(Value *);

  /* Explicit Map manipulation functions */

  /* Single function that adds base/bound/key to the pointer map,
   * first argument - pointer operand
   * second argument - associated base
   * third argument - associated bound
   * fourth argument - associated key
   * fifth argument - associated lock
   */
  // void associateBaseBoundKeyLock(Value*, Value*, Value*, Value*, Value*);
  /* XMM mode functions for base/bound and key/lock extraction */
  // void associateXMMBaseBoundKeyLock(Value*, Value*, Value*);

  void associateBaseBound(Value *, Value *, Value *);
  void associateKeyLock(Value *, Value *, Value *);
  void associateAggregateBase(Value *Val, TinyPtrVector<Value *> &Bases);
  void associateAggregateBound(Value *Val, TinyPtrVector<Value *> &Bounds);
  void associateAggregateBaseBound(Value *Val, TinyPtrVector<Value *> &Bases,
                                   TinyPtrVector<Value *> &Bounds);
  void associateAggregateKeyLock(Value *Val, TinyPtrVector<Value *> &Keys,
                                 TinyPtrVector<Value *> &Locks);
  void associateMetadata(Value *, Value *, Value *, Value *, Value *);
  void associateMetadata(Value *Val, const SoftBoundCETSMetadata &Metadata);
  void associateAggregateMetadata(Value *, TinyPtrVector<Value *> &,
                                  TinyPtrVector<Value *> &,
                                  TinyPtrVector<Value *> &,
                                  TinyPtrVector<Value *> &);

  enum MetadataType { Base, Bound, Key, Lock };
  bool isValidMetadata(Value *, MetadataType);

  Value *createMetadataVector(ArrayRef<Value *> SingleMetadataVals,
                              Instruction *InsertAt);
  SmallVector<Value *, 8> extractVectorValues(Value *MetadataVector,
                                              Instruction *InsertAt);
  SmallVector<Value *, 8> extractVectorBases(Value *Val, Instruction *InsertAt);
  SmallVector<Value *, 8> extractVectorBounds(Value *Val,
                                              Instruction *InsertAt);
  SmallVector<Value *, 8> extractVectorKeys(Value *Val, Instruction *InsertAt);
  SmallVector<Value *, 8> extractVectorLocks(Value *Val, Instruction *InsertAt);

  /* Returns the base associated with the pointer value */
  Value *getAssociatedBase(Value *);
  ArrayRef<Value *> getAssociatedBases(Value *);

  /* Returns the bound associated with the pointer value */
  Value *getAssociatedBound(Value *);
  ArrayRef<Value *> getAssociatedBounds(Value *);

  Value *getAssociatedKey(Value *);
  ArrayRef<Value *> getAssociatedKeys(Value *);

  Value *getAssociatedLock(Value *);
  ArrayRef<Value *> getAssociatedLocks(Value *);

  SmallVector<Value *> unpackMetadataArray(ArrayRef<Value *>, Instruction *);
  TinyPtrVector<Value *> packMetadataArray(ArrayRef<Value *>, Type *Ty,
                                           Instruction *);

  SmallVector<std::tuple<uint8_t, uint8_t>, 8> getMetadataOrder(Type *Ty);

  template <typename T>
  TinyPtrVector<T *> createDummyMetadata(Type *Ty, Constant *Metadatum);
  TinyPtrVector<Value *> createDummyLocks(Type *Ty);
  void associateOmnivalidMetadata(Value *Val);
  void associateInvalidMetadata(Value *Val);

  bool checkBaseBoundMetadataPresent(Value *);
  bool checkMetadataPresent(Value *);

  bool checkKeyLockMetadataPresent(Value *);

  /* Function to add a call to m_store_base_bound_func */
  void insertPointerMetadataStore(Value *, Value *, Value *, Value *, Value *,
                                  Instruction *);
  void insertVectorMetadataStore(Value *, Value *, Value *, Value *, Value *,
                                 Instruction *);

  void addStoreXMMBaseBoundFunc(Value *, Value *, Value *, Instruction *);

  void setFunctionPtrBaseBound(Value *, Instruction *);

  void replaceAllInMap(std::map<Value *, Value *> &, Value *, Value *);

  void castAddToPhiNode(PHINode *, Value *, BasicBlock *,
                        std::map<Value *, Value *> &, Value *);

  void getConstantExprBaseBound(Constant *, Value *&, Value *&);

  Value *castAndReplaceAllUses(Value *, Value *, Instruction *);

  bool checkIfNonCallUseOfFunction(Function *);

  /* Other helper functions */

  Value *introduceGEPWithLoad(Value *, int, Instruction *);
  Value *storeShadowStackBaseForFunctionArgs(Instruction *, int);
  Value *storeShadowStackBoundForFunctionArgs(Instruction *, int);
  Value *storeShadowStackKeyForFunctionArgs(Instruction *, int);
  Value *storeShadowStackLockForFunctionArgs(Instruction *, int);

  Value *retrieveShadowStackBaseForFunctionArgs(Instruction *, int);
  Value *retrieveShadowStackBoundForFunctionArgs(Instruction *, int);
  Value *retrieveShadowStackKeyForFunctionArgs(Instruction *, int);
  Value *retrieveShadowStackLockForFunctionArgs(Instruction *, int);

  Value *introduceGlobalLockFunction(Instruction *);
  void introspectMetadata(Function *, Value *, Instruction *, int);
  size_t introduceShadowStackLoads(Value *, Instruction *, int);
  void introduceShadowStackAllocation(CallBase *, int);
  size_t introduceShadowStackStores(Value *, Instruction *, int);
  void introduceShadowStackDeallocation(CallBase *, Instruction *);
  size_t getNumPointerArgs(const CallBase *CB);

  void checkIfRetTypePtr(Function *, bool &);
  Instruction *getReturnInst(Function *, int);

  //
  // Method: getNextInstruction
  //
  // Description:
  // This method returns the next instruction after the input instruction.
  //

  Instruction *getNextInstruction(Instruction *I) {
    if (I->isTerminator())
      return I;
    return I->getNextNode();
  }

  const Type *getStructType(const Type *);
  ConstantInt *getSizeOfType(Type *);

  Value *castToVoidPtr(Value *Ptr, IRBuilder<> &IRB);
  Value *castToVoidPtr(Value *, Instruction *);
  bool checkGEPOfInterestSB(GetElementPtrInst *);
  void handleReturnInst(ReturnInst *);

public:
  static char ID;

  /* INITIALIZE_PASS(SoftBoundCETSPass, "softboundcetspass", */
  /*               "SoftBound CETS for memory safety", false, false) */

  SoftBoundCETSPass(StringRef BlacklistFile = "")
      : ModulePass(ID), BlacklistFile(BlacklistFile) {}

  llvm::StringRef getPassName() const override { return "SoftBoundCETSPass"; }

  void getAnalysisUsage(AnalysisUsage &au) const override {
    au.addRequired<DominatorTreeWrapperPass>();
    au.addRequired<LoopInfoWrapperPass>();
    au.addRequired<TargetLibraryInfoWrapperPass>();
  }
};

#endif
