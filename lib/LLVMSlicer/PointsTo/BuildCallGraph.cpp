#include "llvm/Analysis/Andersen/Andersen.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include <map>

#include "BuildCallGraph.h"
#include "RuleExpressions.h"

#include "../Languages/LLVM.h"

namespace llvm {
namespace ptr {
typedef PointsToSets::PointsToSet PTSet;
typedef PointsToSets::Pointer Ptr;

static bool applyRule(PointsToSets &S,
                      ASSIGNMENT<VARIABLE<const llvm::Value *>,
                                 VARIABLE<const llvm::Value *>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  const PTSet &R = S[Ptr(rval, -1)];
  const std::size_t old_size = L.size();

  std::copy(R.begin(), R.end(), std::inserter(L, L.end()));

  return old_size != L.size();
}

static int64_t accumulateConstantOffset(const GetElementPtrInst *gep,
                                        const DataLayout &DL, bool &isArray) {
  int64_t off = 0;

  for (gep_type_iterator GTI = gep_type_begin(gep), GTE = gep_type_end(gep);
       GTI != GTE; ++GTI) {
    ConstantInt *OpC = dyn_cast<ConstantInt>(GTI.getOperand());
    if (!OpC) /* skip non-const array indices */
      continue;
    if (OpC->isZero())
      continue;

    int64_t ElementIdx = OpC->getSExtValue();

    // Handle a struct index, which adds its field offset to the pointer.
    if (StructType *STy = dyn_cast<StructType>(*GTI)) {
      const StructLayout *SL = DL.getStructLayout(STy);
      off += SL->getElementOffset(ElementIdx);
      continue;
    } else if (SequentialType *STy = dyn_cast<SequentialType>(*GTI)) {
      off += ElementIdx * DL.getTypeStoreSize(GTI.getIndexedType());
      isArray = true;
      continue;
    }
#ifdef FIELD_DEBUG
    errs() << "skipping " << OpC->getValue() << " in ";
    gep->dump();
#endif
  }

  return off;
}

static bool checkOffset(const DataLayout &DL, const Value *Rval, uint64_t sum) {
  if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(Rval)) {
    if (GV->hasInitializer() &&
        sum >= DL.getTypeAllocSize(GV->getInitializer()->getType()))
      return false;
  } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(Rval)) {
    if (!AI->isArrayAllocation() &&
        sum >= DL.getTypeAllocSize(AI->getAllocatedType()))
      return false;
  }

  return true;
}

static bool applyRule(PointsToSets &S, const llvm::DataLayout &DL,
                      ASSIGNMENT<VARIABLE<const llvm::Value *>,
                                 GEP<VARIABLE<const llvm::Value *>>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  const std::size_t old_size = L.size();

  const GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(rval);
  const llvm::Value *op = elimConstExpr(gep->getPointerOperand());
  bool isArray = false;
  int64_t off = accumulateConstantOffset(gep, DL, isArray);

  if (hasExtraReference(op)) {
    L.insert(Ptr(op, off)); /* VAR = REF */
  } else {
    const PTSet &R = S[Ptr(op, -1)];
    for (PTSet::const_iterator I = R.begin(), E = R.end(); I != E; ++I) {
      assert(I->second >= 0);

      /* disable recursive structures */
      if (L.count(*I))
        continue;

      const Value *Rval = I->first;

      if (off && (isa<Function>(Rval) || isa<ConstantPointerNull>(Rval)))
        continue;

      int64_t sum = I->second + off;

      if (!checkOffset(DL, Rval, sum))
        continue;

      unsigned int sameCount = 0;
      for (PTSet::const_iterator II = L.begin(), EE = L.end(); II != EE; ++II) {
        if (II->first == Rval)
          if (++sameCount >= 5)
            break;
      }

      if (sameCount >= 3) {
#ifdef DEBUG_CROPPING
        errs() << "dropping GEP ";
        gep->dump();
        errs() << "\tHAVE " << off << "+"
               << " OFF=" << I->second << " ";
        Rval->dump();
#endif
        continue;
      }

      if (sum < 0) {
        assert(I->second >= 0);
#ifdef DEBUG_CROPPING
        errs() << "variable index, cropping to 0: " << I->second << "+" << off
               << "\n\t";
        gep->dump();
        errs() << "\tPTR=";
        Rval->dump();
#endif
        sum = 0;
      }

      /* an unsoundness :) */
      if (isArray && sum > 64)
        sum = 64;

      L.insert(Ptr(Rval, sum)); /* V = V */
    }
  }

  return old_size != L.size();
}

static bool
applyRule(PointsToSets &S,
          ASSIGNMENT<VARIABLE<const llvm::Value *>,
                     REFERENCE<VARIABLE<const llvm::Value *>>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  const std::size_t old_size = L.size();

  L.insert(Ptr(rval, 0));

  return old_size != L.size();
}

static bool
applyRule(PointsToSets &S,
          ASSIGNMENT<VARIABLE<const llvm::Value *>,
                     DEREFERENCE<VARIABLE<const llvm::Value *>>> const &E,
          const int idx = -1) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument().getArgument();
  PTSet &L = S[Ptr(lval, idx)];
  PTSet &R = S[Ptr(rval, -1)];
  const std::size_t old_size = L.size();

  for (PTSet::const_iterator i = R.begin(); i != R.end(); ++i) {
    PTSet &X = S[*i];
    std::copy(X.begin(), X.end(), std::inserter(L, L.end()));
  }

  return old_size != L.size();
}

static bool applyRule(PointsToSets &S,
                      ASSIGNMENT<DEREFERENCE<VARIABLE<const llvm::Value *>>,
                                 VARIABLE<const llvm::Value *>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  PTSet &R = S[Ptr(rval, -1)];
  bool change = false;

  for (PTSet::const_iterator i = L.begin(); i != L.end(); ++i) {
    PTSet &X = S[*i];
    const std::size_t old_size = X.size();

    std::copy(R.begin(), R.end(), std::inserter(X, X.end()));
    change = change || X.size() != old_size;
  }

  return change;
}

static bool
applyRule(PointsToSets &S,
          ASSIGNMENT<DEREFERENCE<VARIABLE<const llvm::Value *>>,
                     REFERENCE<VARIABLE<const llvm::Value *>>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  bool change = false;

  for (PTSet::const_iterator i = L.begin(); i != L.end(); ++i) {
    PTSet &X = S[*i];
    const std::size_t old_size = X.size();

    X.insert(Ptr(rval, 0));
    change = change || X.size() != old_size;
  }

  return change;
}

static bool
applyRule(PointsToSets &S,
          ASSIGNMENT<DEREFERENCE<VARIABLE<const llvm::Value *>>,
                     DEREFERENCE<VARIABLE<const llvm::Value *>>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  bool change = false;

  for (PTSet::const_iterator i = L.begin(); i != L.end(); ++i)
    if (applyRule(S, (ruleVar(i->first) = *ruleVar(rval)).getSort(), i->second))
      change = true;

  return change;
}

static bool applyRule(PointsToSets &S,
                      ASSIGNMENT<VARIABLE<const llvm::Value *>,
                                 ALLOC<const llvm::Value *>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  const std::size_t old_size = L.size();

  L.insert(Ptr(rval, 0));

  return old_size != L.size();
}

static bool applyRule(PointsToSets &S,
                      ASSIGNMENT<VARIABLE<const llvm::Value *>,
                                 NULLPTR<const llvm::Value *>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  const std::size_t old_size = L.size();

  L.insert(Ptr(rval, 0));

  return old_size != L.size();
}

static bool applyRule(PointsToSets &S,
                      ASSIGNMENT<DEREFERENCE<VARIABLE<const llvm::Value *>>,
                                 NULLPTR<const llvm::Value *>> const &E) {
  const llvm::Value *lval = E.getArgument1().getArgument().getArgument();
  const llvm::Value *rval = E.getArgument2().getArgument();
  PTSet &L = S[Ptr(lval, -1)];
  bool change = false;

  for (PTSet::const_iterator i = L.begin(); i != L.end(); ++i) {
    PTSet &X = S[*i];
    const std::size_t old_size = X.size();

    X.insert(Ptr(rval, 0));
    change = change || X.size() != old_size;
  }

  return change;
}

static bool applyRule(PointsToSets &S, DEALLOC<const llvm::Value *>) {
  return false;
}

static bool applyRules(const RuleCode &RC, PointsToSets &S,
                       const llvm::DataLayout &DL) {
  const llvm::Value *lval = RC.getLvalue();
  const llvm::Value *rval = RC.getRvalue();

  switch (RC.getType()) {
  case RCT_VAR_ASGN_ALLOC:
    return applyRule(S, (ruleVar(lval) = ruleAllocSite(rval)).getSort());
  case RCT_VAR_ASGN_NULL:
    return applyRule(S, (ruleVar(lval) = ruleNull(rval)).getSort());
  case RCT_VAR_ASGN_VAR:
    return applyRule(S, (ruleVar(lval) = ruleVar(rval)).getSort());
  case RCT_VAR_ASGN_GEP:
    return applyRule(S, DL, (ruleVar(lval) = ruleVar(rval).gep()).getSort());
  case RCT_VAR_ASGN_REF_VAR:
    return applyRule(S, (ruleVar(lval) = &ruleVar(rval)).getSort());
  case RCT_VAR_ASGN_DREF_VAR:
    return applyRule(S, (ruleVar(lval) = *ruleVar(rval)).getSort());
  case RCT_DREF_VAR_ASGN_NULL:
    return applyRule(S, (*ruleVar(lval) = ruleNull(rval)).getSort());
  case RCT_DREF_VAR_ASGN_VAR:
    return applyRule(S, (*ruleVar(lval) = ruleVar(rval)).getSort());
  case RCT_DREF_VAR_ASGN_REF_VAR:
    return applyRule(S, (*ruleVar(lval) = &ruleVar(rval)).getSort());
  case RCT_DREF_VAR_ASGN_DREF_VAR:
    return applyRule(S, (*ruleVar(lval) = *ruleVar(rval)).getSort());
  case RCT_DEALLOC:
    return applyRule(S, ruleDeallocSite(RC.getValue()).getSort());
  default:
    assert(0);
  }
}

static Andersen *andersen = nullptr;
static DetectParametersPass *DPP = nullptr;

PointsToSets &computePointsToSets(const SimpleCallGraphInit &callgraph, PointsToSets &S) {
  legacy::PassManager *PM = new legacy::PassManager();
  DPP = new DetectParametersPass();
  andersen = new Andersen();
  PM->add(DPP);
  PM->add(andersen);
  PM->run(callgraph.getModule());

  // FIXME: Passmanager can't be deallocated here ('andersen' is used later)
  //    delete(PM);
  //  return pruneByType(fixpoint(P, S));
  return S;
}

const PTSet &getPointsToSet(const llvm::Value *const &memLoc,
                            const PointsToSets &S, const int idx) {
  const PointsToSets::const_iterator it = S.find(Ptr(memLoc, idx));
  if (it == S.end()) {
    std::vector<const llvm::Value *> PT;
    andersen->getPointsToSet(memLoc, PT);

    static const PTSet emptySet;
    if (PT.size() == 0) {
      return emptySet;
    }

    PTSet *newSet = new PTSet();

    for (std::vector<const llvm::Value *>::iterator p_it = PT.begin();
         p_it != PT.end(); ++p_it) {
      newSet->insert(PointsToSets::Pointee(*p_it, -1));
    }

    ((PointsToSets &)S)[PointsToSets::Pointer(memLoc, -1)] = *newSet;

    return *newSet;
  }
  return it->second;
}

SimpleCallGraph &getSimpleCallGraph() { return andersen->getCallGraph(); }

Andersen *getAndersen() { return andersen; }

DetectParametersPass &getDetectParametersPass() { return *DPP; }

SimpleCallGraphInit::SimpleCallGraphInit(Module &M) : M(M) {
  errs() << "[+]init ptr::ProgramStructure\n";
  for (Module::const_global_iterator g = M.global_begin(), E =
  M.global_end();
       g != E; ++g) {
    errs() << "[i]g: " << g->getName() << "\n";
    if (isGlobalPointerInitialization(&*g))
      detail::toRuleCode(&*g, std::back_inserter(this->getContainer()));
  }
  errs() << "[i]get callMap of Module\n";

  for (Module::const_iterator f = M.begin(); f != M.end(); ++f) {
    if (f->isIntrinsic() || f->isDeclaration()) {
      continue;
    }

    for (const_inst_iterator i = inst_begin(f), E = inst_end(f); i != E; ++i) {
      if (const CallInst *CI = dyn_cast<CallInst>(&*i)) {
        if (!isInlineAssembly(CI) && !callToMemoryManStuff(CI) &&
            CI->getCalledFunction() && CI->getCalledFunction()->hasName()) {
          std::string funcName = CI->getCalledFunction()->getName();
          if (!getSimpleCallGraph().containtsEdge(CI, funcName)) {
            getSimpleCallGraph().addCallEdge(CI, funcName);
          }
        }
      }
    }
  }
  errs() << "[+]init ptr::ProgramStructure end\n";
}
} // namespace ptr
} // namespace llvm
