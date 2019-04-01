#include <string>
#include <set>
#include "sparsehash/dense_hash_map"
#include "sparsehash/dense_hash_set"
#include "sparsehash/sparse_hash_map"
#include "sparsehash/sparse_hash_set"
#include <float.h>
#include <map>
#include <mutex>
#include <pthread.h>
#include <tuple>
#include <unordered_set>
#include <utility> /* pair */

#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SparseSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Value.h"

#include "../Backtrack/Constraint.h"
#include "../Backtrack/Path.h"
#include "../Backtrack/Rule.h"
#include "../Modifies/Modifies.h"
#include "../PointsTo/PointsTo.h"
#include "../Slicing/PostDominanceFrontier.h"
#define INC_MAX FLT_MAX
using namespace llvm;

namespace llvm {
namespace beta {
typedef float IncType_t;
class FunctionIntraDFA;
class InsInfo;
class StructSliceInfo;

class InsInfoProvider {
public:
  virtual ~InsInfoProvider(){};

  virtual void addInitialSlicingCriterion(const Instruction *C) = 0;

  virtual InsInfo *getInsInfo(const Instruction *I) = 0;
};

struct PointeeHash {
  size_t operator()(const llvm::ptr::PointsToSets::Pointee &x) const {
    std::hash<const Value *> h;
    return h(x.first);
  }
};

typedef google::sparse_hash_set<llvm::ptr::PointsToSets::Pointee, PointeeHash>
    ValSet;
class StructSliceInfo {
public:
  StructSliceInfo(int64_t baseOffset, const Value *accessInstruction)
      : accessInstruction(accessInstruction), baseOffset(baseOffset) {}

  StructSliceInfo(const StructSliceInfo &s) {
    accessInstruction = s.accessInstruction;
    basePointers = s.basePointers;
    baseOffset = s.baseOffset;
    locations = s.locations;
  }

  const Value *accessInstruction;
  ptr::PointsToSets::PointsToSet basePointers;
  int64_t baseOffset;
  std::set<ptr::PointsToSets::Pointee> locations;

  bool operator<(const StructSliceInfo &rhs) const {
    if (accessInstruction != rhs.accessInstruction)
      return true;
    if (basePointers != rhs.basePointers)
      return true;
    if (baseOffset != rhs.baseOffset)
      return true;
    if (locations != rhs.locations)
      return true;
    return false;
  }
};

class InsInfo {
private:
  typedef llvm::ptr::PointsToSets::Pointee Pointee;

public:
  typedef google::sparse_hash_set<const Value *> ValSet_t;
  //    typedef std::map<const Value*, std::unique_ptr<ValSet_t>> ValMapSet_t;
  typedef google::sparse_hash_map<const Value *, ValSet_t> ValMapSet_t;
  typedef google::sparse_hash_map<const Value *, IncType_t> IncMap_t;
  typedef std::set<StructSliceInfo *> StructSliceInfoSet_t;
  typedef google::sparse_hash_map<const Value *, StructSliceInfoSet_t>
      SliceInfoSetMap_t;
  typedef google::sparse_hash_set<int64_t> Int64Set_t;
  typedef google::sparse_hash_map<const Value *, Int64Set_t> DefOffsets_t;
  typedef google::sparse_hash_set<const Instruction *> InstSet_t;
  typedef std::pair<const CallInst *, const Instruction *> CallParamPair_t;

  InsInfo(const llvm::Instruction *i, const llvm::ptr::PointsToSets &PS,
          const llvm::mods::Modifies &MOD);

  virtual ~InsInfo() {
  }

  const Instruction *getIns() const { return ins; }

  bool addRC(const Pointee &var, const Value *src, InsInfoProvider *provider,
             IncType_t RCInc = INC_MAX);

  bool addRC(const Pointee &var, const ValSet_t &sources,
             InsInfoProvider *provider, IncType_t RCInc = INC_MAX);

  bool addDEF(const Pointee &var);

  bool addREF(const Pointee &var, IncType_t RefInc = INC_MAX);

  void addRCStruct(const Value *ref, const StructSliceInfo *ssi);

  IncType_t getRCInc(const Pointee &var);

  IncType_t getREFInc(const Pointee &var);

  void deslice(FunctionIntraDFA *FIDFA);

  ValSet::const_iterator RC_begin() const { return RC.begin(); }

  ValSet::const_iterator RC_end() const { return RC.end(); }

  ValSet::const_iterator DEF_begin() const { return DEF.begin(); }

  ValSet::const_iterator DEF_end() const { return DEF.end(); }

  ValSet::const_iterator REF_begin() const { return REF.begin(); }

  ValSet::const_iterator REF_end() const { return REF.end(); }

  static StructSliceInfoSet_t::const_iterator defaultStructIterator;

  StructSliceInfoSet_t::const_iterator REFStruct_begin(const Value *r) {
    if (REFStructInfos.find(r) == REFStructInfos.end()) {
      return defaultStructIterator;
    }
    return REFStructInfos[r].begin();
  }

  StructSliceInfoSet_t::const_iterator REFStruct_end(const Value *r) {
    if (REFStructInfos.find(r) == REFStructInfos.end()) {
      return defaultStructIterator;
    }
    return REFStructInfos[r].end();
  }

  StructSliceInfoSet_t::const_iterator RCStruct_begin(const Value *rc) {
    if (RCStructInfos.find(rc) == RCStructInfos.end()) {
      return defaultStructIterator;
    }
    return RCStructInfos[rc].begin();
  }

  StructSliceInfoSet_t::const_iterator RCStruct_end(const Value *rc) {
    if (RCStructInfos.find(rc) == RCStructInfos.end()) {
      return defaultStructIterator;
    }
    return RCStructInfos[rc].end();
  }

  bool isSliced() const { return sliced; }

  void dump(bool def = false, bool ref = false, bool rc = false,
            bool pred = false);

  const ValSet_t &getRCSource(const Pointee &var) {
    //        assert(RCSources.find(var.first) != RCSources.end());
    static ValSet_t emptySet;
    if (RCSources.find(var.first) == RCSources.end())
      return emptySet;
    ValSet_t &set = RCSources[var.first];
    return set;
  }

  void addSlicedPredecessor(const Pointee &RC, const Instruction *Pred,
                            InsInfoProvider *provider);

  bool backtrack(InsInfoProvider *provider,
                 llvm::slicing::PathElementBase *pathElement,
                 std::vector<llvm::slicing::Path *> &paths,
                 std::mutex &pathLock, llvm::slicing::Rule &rule);

  void addTranslation(const Value *from, const Value *to) {
    ValSet_t &t = translations[from];
    t.insert(to);
  }

  bool hasTranslation(const Value *v) {
    return translations.find(v) != translations.end();
  }

  StructSliceInfoSet_t &getDEFStructSliceInfos() { return DEFStructInfos; }

  void addReturnPred(const Instruction *ret) {
    if (ins->getOpcode() != Instruction::Call)
      llvm_unreachable(
          "'return' predecessors can only be added for call instructions");
    returnPreds.insert(ret);
  }

  DefOffsets_t &getDEFOffset() { return defOffsets; }

  void addUP(const Value *up) { Up.insert(up); }

  void addUPSuccessor(const Value *succ, const Value *rc) {
    UpSuccessors[rc].insert(succ);
  }

private:
  void addDEFArray(const ptr::PointsToSets &PS, const Value *V,
                   uint64_t lenConst);

  void addREFArray(const ptr::PointsToSets &PS, const Value *V,
                   uint64_t lenConst);

  void handleVariousFuns(const ptr::PointsToSets &PS, const CallInst *C);

  const llvm::Instruction *ins;
  // RC: relevant variables; SC: relevant statements; BC: branch statements;
  ValSet RC, DEF, REF;
  IncMap_t RefIncMap;
  IncMap_t RCIncMap;
  bool sliced;

  StructSliceInfoSet_t DEFStructInfos;
  SliceInfoSetMap_t REFStructInfos;
  SliceInfoSetMap_t RCStructInfos;

  ValMapSet_t RCSources;
  std::map<const Value *, std::set<const Instruction *>> SlicedPredecessors;

  // If the we reach this instruction tracing a value of the key set in
  // 'translations' we create a path for each value in the value set of this key
  ValMapSet_t translations;

  std::set<const Instruction *> returnPreds;

  DefOffsets_t defOffsets;
  // Contains those instructions that use some of the RCs and have this
  // instructions as RC_source
  ValSet_t Up;
  ValMapSet_t UpSuccessors;
};

class FunctionIntraDFA {
  friend class InsInfo;

  typedef llvm::ptr::PointsToSets::Pointee Pointee;

public:
  typedef google::sparse_hash_map<const llvm::Instruction *, InsInfo *>
      InsInfoMap;

  FunctionIntraDFA(llvm::Function &F, llvm::ModulePass *MP,
                   const llvm::ptr::PointsToSets &PT,
                   const llvm::mods::Modifies &mods,
                   InsInfoProvider *insInfoProvider = NULL)
      : infosInitialized(false), fun(F), MP(MP),
        insInfoProvider(insInfoProvider), mods(mods), PS(PT) {}

  ~FunctionIntraDFA();

  void initializeInfos();

  ValSet::const_iterator relevant_begin(const llvm::Instruction *I) const {
    return getInsInfo(I)->RC_begin();
  }

  ValSet::const_iterator relevant_end(const llvm::Instruction *I) const {
    return getInsInfo(I)->RC_end();
  }

  ValSet::const_iterator REF_begin(const llvm::Instruction *I) const {
    return getInsInfo(I)->REF_begin();
  }

  ValSet::const_iterator REF_end(const llvm::Instruction *I) const {
    return getInsInfo(I)->REF_end();
  }

  template <typename FwdValueIterator>
  bool addCriterion(const llvm::Instruction *ins, FwdValueIterator b,
                    FwdValueIterator const e, InsInfoProvider *callback = NULL,
                    InsInfo::ValMapSet_t rcSources = InsInfo::ValMapSet_t(),
                    InsInfo::IncMap_t IncMap = InsInfo::IncMap_t(),
                    bool desliceIfChanged = false) {
    initializeInfos();
    InsInfo *ii = getInsInfo(ins);
    bool change = false;

    const CallInst *callInst = dyn_cast<const CallInst>(ins);

    InsInfo::ValSet_t callRCSource;
    callRCSource.insert(ins);

    for (; b != e; ++b) {
      InsInfo::IncMap_t::iterator i = IncMap.find(b->first);
      bool found = i != IncMap.end();
      IncType_t v = found ? i->second : INC_MAX;

      if (callInst) {
        if (ii->addRC(*b, callRCSource, callback, v))
          change = true;
      } else {
        if (ii->addRC(*b, rcSources[b->first], callback, v))
          change = true;
      }
    }
    if (change && desliceIfChanged) {
      ii->deslice(this);
      if (callInst && callback) {
        for (auto &rc : rcSources) {
          for (auto &src : rc.second) {
            const Instruction *srcInst = dyn_cast<const Instruction>(src);
            ii->addUPSuccessor(srcInst, rc.first);
            ii->addUP(srcInst);
          }
        }
      }
    }
    return change;
  }

  void addInitialCriterion(const llvm::Instruction *ins,
                           const Pointee &cond = Pointee(0, 0),
                           bool deslice = true) {
    initializeInfos();
    InsInfo *ii = getInsInfo(ins);
    if (cond.first) {
      ii->addRC(cond, ins, NULL, 0.0);
    }
    ii->deslice(this);
    if (insInfoProvider && cond.first) {
      if (const Instruction *C = dyn_cast<const Instruction>(cond.first)) {
        insInfoProvider->addInitialSlicingCriterion(C);
      }
    }
  }

  void addSkipAssert(const llvm::CallInst *CI) { skipAssert.insert(CI); }

  bool shouldSkipAssert(const llvm::CallInst *CI) {
    return skipAssert.count(CI);
  }

  InsInfo *getInsInfo(const llvm::Instruction *i) const {
    assert(infosInitialized);
    InsInfoMap::const_iterator I = insInfoMap.find(i);

    // TODO: should we check this before calling?
    if (I == insInfoMap.end())
      return NULL;
    return I->second;
  }
  void calculateStaticSlice();
  

  bool isInitialized() const { return infosInitialized; }
  void removeUndefBranches(ModulePass *MP, Function &F);
  void removeUndefCalls(ModulePass *MP, Function &F);
  void removeUndefCalls(ModulePass *MP, inst_iterator I);
  void removeUndefs(ModulePass *MP, Function &F);
  
  void dumpInfos();

private:
  std::mutex initLock;
  bool infosInitialized;
  std::mutex slicerLock;
  static std::mutex passLock;

  llvm::Function &fun;
  llvm::ModulePass *MP;
  InsInfoMap insInfoMap;
  llvm::SmallSetVector<const llvm::CallInst *, 10> skipAssert;
  InsInfoProvider *insInfoProvider;
  const llvm::mods::Modifies &mods;

  const llvm::ptr::PointsToSets &PS;
  static bool sameValues(const Pointee &val1, const Pointee &val2);

  void crawlBasicBlock(const llvm::BasicBlock *bb);

  bool computeRCi(InsInfo *insInfoi, InsInfo *insInfoj);

  bool computeRCi(InsInfo *insInfoi);

  void computeRC();

  void computeSCi(const llvm::Instruction *i, const llvm::Instruction *j);

  void computeSC();

  bool computeBC();

  bool updateRCSC(PostDominanceFrontier::DomSetType::const_iterator start,
                  PostDominanceFrontier::DomSetType::const_iterator end);
};

bool findInitialCriterion(inst_iterator inst_it, FunctionIntraDFA &DFA,
                          std::vector<llvm::slicing::Rule *> &rules);
}
}