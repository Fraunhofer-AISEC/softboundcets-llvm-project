#include "Utils.h"
#include "llvm/Support/ConvertUTF.h"

size_t countPointersInType(Type *Ty) {
  switch (Ty->getTypeID()) {
  case Type::PointerTyID:
    return 1;
  case Type::StructTyID: {
    size_t Sum = 0;
    for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end();
         I != E; ++I) {
      Sum += countPointersInType(*I);
    }
    return Sum;
  }
  case Type::ArrayTyID: {
    ArrayType *ArrayTy = cast<ArrayType>(Ty);
    return countPointersInType(ArrayTy->getElementType()) *
           ArrayTy->getNumElements();
  }
  case Type::FixedVectorTyID: {
    FixedVectorType *FVTy = cast<FixedVectorType>(Ty);
    return countPointersInType(FVTy->getElementType()) * FVTy->getNumElements();
  }
  // TODO[orthen]: enable this too with ElementCount, isScalar, getValue
  case Type::ScalableVectorTyID: {
    assert(0 && "Counting pointers for scalable vectors not yet handled.");
  }
  default:
    return 0;
  }
}

bool isTypeWithPointers(Type *Ty) {
  switch (Ty->getTypeID()) {
  case Type::PointerTyID:
    return true;
  case Type::StructTyID: {
    for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end();
         I != E; ++I) {
      if (isTypeWithPointers(*I))
        return true;
    }
    return false;
  }
  case Type::ArrayTyID: {
    ArrayType *ArrayTy = cast<ArrayType>(Ty);
    return isTypeWithPointers(ArrayTy->getElementType());
  }
  case Type::FixedVectorTyID: {
    FixedVectorType *FVTy = cast<FixedVectorType>(Ty);
    return isTypeWithPointers(FVTy->getElementType());
  }
  case Type::ScalableVectorTyID: {
    assert(0 && "Counting pointers for scalable vectors not yet handled.");
  }
  default:
    return false;
  }
}

Type *getContainedByValType(Argument *FnArg) {
  PointerType *PointerTy = dyn_cast<PointerType>(FnArg->getType());
  assert(PointerTy && "byval attribute for argument that is not a pointer");
  return PointerTy->getContainedType(0);
}

bool isVectorWithPointers(Type *Ty) {
  auto *VectorTy = dyn_cast<VectorType>(Ty);
  if (VectorTy && VectorTy->getElementType()->isPointerTy()) {
    return true;
  }
  return false;
}

// Count how much metadata (consisting of Base, Bound, Key, Lock value pointers)
// we need during compile time.
// Pointers need 1 metadata, vectors also (metadata of vectors is stored in
// other vectors). Aggregate types need the sum of metadata of their subtypes.
size_t countMetadata(Type *Ty) {
  switch (Ty->getTypeID()) {
  case Type::PointerTyID:
    return 1;
  case Type::StructTyID: {
    size_t Sum = 0;
    for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end();
         I != E; ++I) {
      Sum += countMetadata(*I);
    }
    return Sum;
  }
  case Type::ArrayTyID: {
    ArrayType *ArrayTy = cast<ArrayType>(Ty);
    return countMetadata(ArrayTy->getElementType()) * ArrayTy->getNumElements();
  }
  case Type::FixedVectorTyID: {
    return 1;
  }
  case Type::ScalableVectorTyID: {
    assert(0 && "Counting metadata for scalable vectors not yet handled.");
  }
  default:
    return 0;
  }
}

void collectVarargPointerLoads(Instruction *Root, SmallVector<LoadInst *> &LoadInsts,
                               std::set<Value *> &Visited) {
  if (Visited.count(Root))
    return; // Avoid cycles
  Visited.insert(Root);

  for (auto *Usr : Root->users()) {
    Instruction* I = dyn_cast<Instruction>(Usr);

    if (!I || isa<CallBase>(I))
      continue;
    // Check if the user is a LoadInst and loads a pointer
    if (auto *LI = dyn_cast<LoadInst>(Usr)) {
      if (LI->getType()->isPointerTy()) {
        LoadInsts.push_back(LI); // Collect LoadInst
      }
    }

    // Continue the traversal for other users
    collectVarargPointerLoads(I, LoadInsts, Visited);
  }
}
