/*
 * slice on module, but when
 */

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include <future>
#include <llvm/Analysis/Andersen/DetectParametersPass.h>
#include <llvm/Support/UniqueLock.h>
#include <signal.h>
#include <thread>
#include <utility>

#include "../Backtrack/Constraint.h"
#include "../Backtrack/Path.h"
#include "../Backtrack/Rule.h"
#include "../Callgraph/Callgraph.h"
#include "../Modifies/Modifies.h"
#include "../PointsTo/PointsTo.h"
#include "./FunctionIntraDFA.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IntraDFA/IntraDFA.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"

#define DEBUG_TYPE "intra-dfa"

using namespace llvm;
using namespace llvm::slicing;
using namespace llvm::dfa;

static cl::opt<std::string>
    ReportFilename("r", cl::desc("Path to HTML report output file"),
                   cl::value_desc("report"));

namespace llvm {
namespace dfa {
namespace detail {
typedef ptr::PointsToSets::Pointee Pointee;
typedef std::map<const Pointee, const Pointee> ParamsToArgs;
typedef std::set<Pointee> RelevantSet;

static void fillParamsToArgs(const CallInst *C, const Function *F,
                             ParamsToArgs &toArgs) {
  Function::const_arg_iterator p = F->arg_begin();

  for (unsigned a = 0; a < C->getNumArgOperands(); ++a, ++p) {
    const Value *P = &*p;

    const Value *A = C->getArgOperand(a);
    if (!isConstantValue(A))
      toArgs.insert(ParamsToArgs::value_type(Pointee(P, -1), Pointee(A, -1)));
  }
}

static void getRelevantVarsAtCall(const CallInst *C, const Function *F,
                                  DetectParametersPass *DPP,
                                  const ptr::PointsToSets &PS,
                                  ValSet::const_iterator b,
                                  const ValSet::const_iterator &e,
                                  RelevantSet &out, FunctionIntraDFA *FIDFA,
                                  InsInfo *entry, InsInfo::IncMap_t &RCInc,
                                  InsInfo::SliceInfoSetMap_t &structSliceInfos,
                                  InsInfo::ValMapSet_t &RCSources) {
  assert(!isInlineAssembly(C) && "Inline assembly is not supported!");
  ParamsToArgs toArgs;
  fillParamsToArgs(C, F, toArgs);

  DetectParametersPass::ParameterAccessPairSet_t Reg =
      DPP->getParameterRegisterIndexes((Function *)F);

  for (; b != e; ++b) {
    const Value *loc =
        ptr::getAndersen()->getNodeFactory().getLocation(b->first);
    if (loc) {
      if (const Instruction *locInst = dyn_cast<const Instruction>(loc)) {
        if (loc->getName().find("init") != StringRef::npos &&
            locInst->getParent()->getParent() == F) {
          RCSources.erase(b->first);
          continue;
        }
      }
    }

    bool foundParameter = false;
    if (const Instruction *I = dyn_cast<const Instruction>(b->first)) {
      if (I->getOpcode() == Instruction::Load) {

        for (DetectParametersPass::ParameterAccessPairSet_t::iterator Reg_it =
                 Reg.begin();
             Reg_it != Reg.end(); ++Reg_it) {
          if (I == Reg_it->second) {
            DetectParametersPass::UserSet_t Pre =
                DetectParametersPass::getRegisterValuesBeforeCall(Reg_it->first,
                                                                  C, true);
            for (DetectParametersPass::UserSet_t::iterator Pre_it = Pre.begin();
                 Pre_it != Pre.end(); ++Pre_it) {

              Instruction *I = (Instruction *)(*Pre_it);
              Pointee p(*Pre_it, -1);

              const InsInfo::ValSet_t src = entry->getRCSource(*b);
              if (src.size() == 0) {
                continue;
              }
              RCSources[p.first] = src;
              RCSources[p.first].insert(I);

              out.insert(p);

              structSliceInfos[p.first].insert(entry->RCStruct_begin(p.first),
                                               entry->RCStruct_end(p.first));

              RCInc[p.first] = RCInc[(*b).first];

              foundParameter = true;
            }
          }
        }
      }
    }

    const InsInfo::ValSet_t src = entry->getRCSource(*b);
    if (src.size() == 0) {
      continue;
    }
    RCSources[b->first].insert(src.begin(), src.end());

    // Copy all values that were not matched as parameters too
    structSliceInfos[b->first].insert(entry->RCStruct_begin(b->first),
                                      entry->RCStruct_end(b->first));

    if (foundParameter)
      continue;

    ParamsToArgs::const_iterator it = toArgs.find(*b);
    if (it != toArgs.end())
      out.insert(it->second);
    else if (!isLocalToFunction(b->first, F))
      out.insert(*b);
  }
  return;
}

static void getRelevantVarsAtExit(
    const CallInst *C, const ReturnInst *R, DetectParametersPass *DPP,
    const ptr::PointsToSets &PS, ValSet::const_iterator b,
    const ValSet::const_iterator &e, RelevantSet &out, InsInfo *succInfo,
    InsInfo *callInfo, InsInfo::IncMap_t &RCInc,
    InsInfo::SliceInfoSetMap_t &structSliceInfos,
    InsInfo::ValMapSet_t &RCSources, const mods::Modifies &MOD) {
  assert(!isInlineAssembly(C) && "Inline assembly is not supported!");

  DetectParametersPass::ParameterAccessPairSet_t Ret =
      DPP->getReturnRegisterIndexes((Function *)R->getParent()->getParent());
  if (callToVoidFunction(C)) {
    for (ValSet::const_iterator it = b; it != e; ++it) {
      // Check if the relevant variable is modified in this function
      bool intersect = false;
      mods::Modifies::mapped_type const &M =
          getModSet(R->getParent()->getParent(), MOD);
      for (mods::Modifies::mapped_type::const_iterator v = M.begin();
           v != M.end(); ++v) {
        if (v->first == (*it).first) {
          intersect = true;
          break;
        }
      }

      // Relevant variable won't be modified anywhere here...
      if (!intersect) {
        continue;
      }

      RCSources[it->first].insert(R);
      structSliceInfos[it->first].insert(callInfo->RCStruct_begin(it->first),
                                         callInfo->RCStruct_end(it->first));
      out.insert(*it);

      structSliceInfos[it->first].insert(callInfo->RCStruct_begin(it->first),
                                         callInfo->RCStruct_end(it->first));
    }
    return;

    for (DetectParametersPass::ParameterAccessPairSet_t::iterator Ret_it =
             Ret.begin();
         Ret_it != Ret.end(); ++Ret_it) {
      DetectParametersPass::UserSet_t Post =
          DetectParametersPass::getRegisterValuesAfterCall(Ret_it->first, C);
      for (DetectParametersPass::UserSet_t::iterator Post_it = Post.begin();
           Post_it != Post.end(); ++Post_it) {
        for (ValSet::const_iterator b_it = b; b_it != e; ++b_it) {
          if (const Instruction *I = dyn_cast<const Instruction>(b_it->first)) {
            if (I == (*Post_it)) {
              Pointee p(Ret_it->second, -1);
              out.insert(p);
              RCInc[p.first] = RCInc[b_it->first];

              const InsInfo::ValSet_t src = succInfo->getRCSource(*b);
              RCSources[p.first] = src;
              //                            RCSources[p.first].insert(callInfo->getIns());
              structSliceInfos[p.first].insert(
                  callInfo->RCStruct_begin(p.first),
                  callInfo->RCStruct_end(p.first));
            }
          }
        }
      }
    }
    return;
  }

  llvm_unreachable("Decompiled code uses void functions only");

  for (; b != e; ++b)
    if (b->first == C) {
      Value *ret = R->getReturnValue();
      if (!ret) {
        return;
      }
      out.insert(Pointee(R->getReturnValue(), -1));
    } else
      out.insert(*b);
}
} // namespace detail

static cl::opt<int> limitCalls("limit-calls", cl::init(0), cl::Hidden);

class IntraDFA : public InsInfoProvider {
public:
  typedef std::map<llvm::Function const *, FunctionIntraDFA *> Slicers;
  typedef std::multimap<llvm::Function const *, llvm::CallInst const *>
      FuncsToCalls;
  typedef std::multimap<llvm::CallInst const *, llvm::Function const *>
      CallsToFuncs;

  IntraDFA(ModulePass *MP, Module &M, const ptr::PointsToSets &PS,
           const callgraph::Callgraph &CG, const mods::Modifies &MOD,
           std::vector<Rule *> rules);
  ~IntraDFA();

  void computeSlice();
  void emit(Function *&f);
  void ruleIteraton();
  bool sliceModule();
  bool sliceFunction(Function *f);

  virtual void addInitialSlicingCriterion(const Instruction *C);
  virtual InsInfo *getInsInfo(const Instruction *I);

  bool addRule(Rule *rule);
  const std::vector<Rule *> getRules() const { return rules; }

private:
  // typedef std::multimap<const llvm::slicing::Rule*, const llvm::Function *> RuleFunctions_t;
  // typedef llvm::SmallVector<RuleFunctions_t, 20> InitFuncs;
  typedef llvm::SmallVector<const llvm::Function *, 20> InitFuncs;
  legacy::PassManager *PM;
  DetectParametersPass *DPP;
  const ptr::PointsToSets &PS;
  const mods::Modifies &MOD;
  std::vector<Rule *> rules;
  std::vector<Rule *> ruleWorklist;

  void buildDicts(const ptr::PointsToSets &PS, const CallInst *c);
  void findInitialCriterions();

  template <typename OutIterator>
  void emitToCalls(llvm::Function const *const f, OutIterator out);
  template <typename OutIterator>
  void emitToExits(llvm::Function const *const f, OutIterator out);

  void runFIDFA(Function &F, const ptr::PointsToSets &PS,
                const callgraph::Callgraph &CG, const mods::Modifies &MOD);

  ModulePass *MP;
  Module &module;
  Slicers slicers;
  std::mutex slicersLock;
  InitFuncs initFuncs;
  FuncsToCalls funcsToCalls;
  CallsToFuncs callsToFuncs;
  std::set<const Instruction *> InitialCriterions;
};

template <typename OutIterator>
void IntraDFA::emitToCalls(const Function *f, OutIterator out) {
  const Instruction *entry = getFunctionEntry(f);
  const ValSet::const_iterator relBgn = slicers[f]->relevant_begin(entry);
  const ValSet::const_iterator relEnd = slicers[f]->relevant_end(entry);

  if (relBgn == relEnd) {
    return;
  }

  bool dump = false;
  if (dump) {
    for (ValSet::const_iterator it = relBgn; it != relEnd; ++it) {
      (*it).first->dump();
    }
  }

  InsInfo::IncMap_t RCInc;
  InsInfo *entryInfo = slicers[f]->getInsInfo(entry);
  for (ValSet::const_iterator i = relBgn; i != relEnd; ++i) {
    double RC_inc = entryInfo->getRCInc(*i);
    RCInc[i->first] = RC_inc;
  }

  FuncsToCalls::const_iterator c, e;
  std::tie(c, e) = funcsToCalls.equal_range(f);

  if (limitCalls && std::distance(c, e) > limitCalls) {
    errs() << "To many calls to function " << f->getName() << " -> skip\n";
    return;
  }

  std::set<std::string> calls;

  for (; c != e; ++c) {
    const CallInst *CI = c->second;
    const Function *g = CI->getParent()->getParent();
    FunctionIntraDFA *FIDFA = slicers[g];

    detail::RelevantSet R;
    InsInfo::SliceInfoSetMap_t structSliceInfos;
    InsInfo::ValMapSet_t rcSources;
    detail::getRelevantVarsAtCall(c->second, f, DPP, PS, relBgn, relEnd, R,
                                  FIDFA, entryInfo, RCInc, structSliceInfos,
                                  rcSources);
    if (R.begin() == R.end()) {
      continue;
    }
    typedef std::set<const Function *> FunctionSet_t;
    std::function<bool(const Value *, const Function *, FunctionSet_t &)>
        isInScope =
            [&](const Value *r, const Function *f, FunctionSet_t &visited) {
              if (visited.find(f) != visited.end()) {
                return false;
              }
              visited.insert(f);

              if (dyn_cast<const StoreInst>(r)) {
                return true;
              }
              if (dyn_cast<const Constant>(r)) {
                return true;
              }

              mods::Modifies::mapped_type const &M = getModSet(f, MOD);
              bool isModified = false;

              for (mods::Modifies::mapped_type::const_iterator v = M.begin();
                   v != M.end(); ++v) {
                if (v->first == r) {
                  isModified = true;
                  break;
                }
              }

              if (isModified) {
              } else {
                FuncsToCalls::const_iterator calledBy_b, callledBy_e;
                std::tie(calledBy_b, callledBy_e) = funcsToCalls.equal_range(f);

                for (; calledBy_b != callledBy_e; ++calledBy_b) {
                  if (isInScope(r, calledBy_b->second->getParent()->getParent(),
                                visited)) {
                    isModified = true;
                    break;
                  }
                }
              }
              return isModified;
            };

    // remove variables which are not inScope
    detail::RelevantSet toRemove;
    for (auto &r : R) {
      FunctionSet_t visited;
      if (!isInScope(r.first, g, visited)) {
        toRemove.insert(r);
      }
    }

    for (auto &rem : toRemove) {
      DEBUG(errs() << "Not modified: "; rem.first->dump());
      R.erase(rem);
    }

    if (!R.size()) {
      DEBUG(errs() << "No relevant variables in scope " << f->getName()
                   << "\n");
      continue;
    }

    FIDFA->initializeInfos();
    InsInfo *CallInfo = FIDFA->getInsInfo(CI);

    if (FIDFA->addCriterion(CI, R.begin(), R.end(), this, rcSources, RCInc,
                            !FIDFA->shouldSkipAssert(CI))) {
      FIDFA->addCriterion(CI, FIDFA->REF_begin(CI), FIDFA->REF_end(CI));
      *out++ = g;
      calls.insert(c->second->getParent()->getParent()->getName().str());
    }

    for (auto &structInfo_it : structSliceInfos) {
      for (auto &ssi_it : structInfo_it.second) {
        CallInfo->addRCStruct(structInfo_it.first, ssi_it);
      }
    }
  }
}

template <typename OutIterator>
void IntraDFA::emitToExits(const Function *f, OutIterator out) {
  typedef std::vector<const CallInst *> CallsVec;

  CallsVec C;
  getFunctionCalls(f, std::back_inserter(C));

  std::set<std::string> calls;

  for (CallsVec::const_iterator c = C.begin(); c != C.end(); ++c) {
    const Instruction *succ = getSuccInBlock(*c);
    const ValSet::const_iterator relBgn = slicers[f]->relevant_begin(succ);
    const ValSet::const_iterator relEnd = slicers[f]->relevant_end(succ);

    InsInfo::IncMap_t RCInc;
    InsInfo *succInfo = slicers[f]->getInsInfo(succ);
    InsInfo *callInfo = slicers[f]->getInsInfo(*c);
    for (ValSet::const_iterator i = relBgn; i != relEnd; ++i) {
      double RC_inc = succInfo->getRCInc(*i);
      RCInc[i->first] = RC_inc;
    }

    CallsToFuncs::const_iterator g, e;
    std::tie(g, e) = callsToFuncs.equal_range(*c);

    for (; g != e; ++g) {
      typedef std::vector<const llvm::ReturnInst *> ExitsVec;
      const Function *callie = g->second;

      ExitsVec E;
      getFunctionExits(callie, std::back_inserter(E));

      for (ExitsVec::const_iterator e = E.begin(); e != E.end(); ++e) {

        detail::RelevantSet R;
        InsInfo::ValMapSet_t RCSources;
        InsInfo::SliceInfoSetMap_t structSliceInfos;
        detail::getRelevantVarsAtExit(*c, *e, DPP, PS, relBgn, relEnd, R,
                                      succInfo, callInfo, RCInc,
                                      structSliceInfos, RCSources, MOD);

        if (relBgn == relEnd) {
          continue;
        }

        slicers[g->second]->initializeInfos();
        InsInfo *exitInfo = slicers[g->second]->getInsInfo(*e);

        callInfo->addReturnPred(*e);
        // FIXME: add real rc sources
        if (slicers[g->second]->addCriterion(*e, R.begin(), R.end(), this,
                                             RCSources, RCInc)) {
          *out++ = g->second;
          calls.insert(g->second->getName());
        }

        for (auto &structInfo_it : structSliceInfos) {
          for (auto &ssi_it : structInfo_it.second) {
            exitInfo->addRCStruct(structInfo_it.first, ssi_it);
          }
        }
      }
    }
  }
}

// build call-function map
void IntraDFA::buildDicts(const ptr::PointsToSets &PS, const CallInst *c) {
  typedef std::vector<const Function *> FunV;
  FunV G;
  getCalledFunctions(c, PS, std::back_inserter(G));

  for (FunV::const_iterator I = G.begin(), E = G.end(); I != E; ++I) {
    const Function *f = *I;
    if (!memoryManStuff(f) && !f->isDeclaration()) {
      funcsToCalls.insert(std::make_pair(f, c));
      callsToFuncs.insert(std::make_pair(c, f));
    }
  }
}


IntraDFA::IntraDFA(ModulePass *MP, Module &M, const ptr::PointsToSets &PS,
                   const callgraph::Callgraph &CG, const mods::Modifies &MOD,
                   std::vector<Rule *> rules)
    : PS(PS), MOD(MOD), MP(MP), module(M), slicers(), initFuncs(),
      funcsToCalls(), callsToFuncs() {
  for (auto &rule : rules) {
    addRule(rule);
  }

  PM = new legacy::PassManager();
  DPP = new DetectParametersPass();
  PM->add(DPP);
  PM->run(M);

  for (Module::iterator f = M.begin(); f != M.end(); ++f) {
    if (!f->isDeclaration() && !memoryManStuff(&*f)) {
      FunctionIntraDFA *FIDFA = new FunctionIntraDFA(*f, MP, PS, MOD, this);
      slicers.insert(Slicers::value_type(&*f, FIDFA));

      // build dicts;
      for (inst_iterator I = inst_begin(*f), E = inst_end(*f); I != E; ++I) {
        if (const CallInst *c = dyn_cast<CallInst>(&*I)) {
          if (isInlineAssembly(c)) {
            continue;
          }
          buildDicts(PS, c);
        }
      }
    }
  }
  // for (Module::iterator f = module.begin(); f != module.end(); ++f) {
  //   if (!f->isDeclaration() && !memoryManStuff(&*f)) {
  //     FunctionIntraDFA *FIDFA = slicers[f];
  //     // find initial criterions.
  //     // findInitialCriterions();
  //     // for (auto &rule : ruleWorklist) {
  //     for (inst_iterator I = inst_begin(*f), E = inst_end(*f); I != E; ++I) {
  //       bool hadAsset = dfa::findInitialCriterion(I, *FIDFA, ruleWorklist);
  //       if (hadAsset) {
  //         // RuleFunctions_t ruleFunctions;
  //         // ruleFunctions.insert(std::make_pair(rule, f));
  //         initFuncs.push_back(f);
  //         FIDFA->initializeInfos();
  //       }
  //     }
  //   }
  // }
}

IntraDFA::~IntraDFA() {
  for (Slicers::const_iterator I = slicers.begin(), E = slicers.end(); I != E;
       ++I) {
    delete I->second;
  }
}


void IntraDFA::ruleIteraton() {
  findInitialCriterions();

  struct FunctionCmp {
    bool operator()(const Function *lhs, const Function *rhs) const {
      return lhs->getName().str().compare(rhs->getName().str());
    }
  };

  typedef std::set<const Function *> Workset;
  Workset tmp;
  for (auto &f : initFuncs) {
  // Q.insert(i);
  // for (WorkSet::const_iterator f = Q.begin(); f != Q.end(); ++f) {
    // If f is in All workset, then it should be skipped.
    // But may be this is useless.
    slicers[f]->calculateStaticSlice();
  }
  for (auto &f : initFuncs) {
    emitToCalls(f, std::inserter(tmp, tmp.end()));
    // errs() << "[+]tmp.size(): " << tmp.size() << "\n";
    emitToExits(f, std::inserter(tmp, tmp.end()));
    // errs() << "[+]exits tmp.size(): " << tmp.size() << "\n";
    if (!tmp.empty()) {
      for (auto &f : tmp) {
        emitToCalls(f, std::inserter(tmp, tmp.end()));
        emitToExits(f, std::inserter(tmp, tmp.end()));
      }
    }
  }
  errs() << "Found " << initFuncs.size() << " initial criterions\n";
  initFuncs.clear();

  // inter slicer workset init here.
  // while (!Q.empty()) {
    // size_t numFunctions = Q.size();
    // errs() << "Num functions: " << numFunctions << "\n";
    // WorkSet tmp;
    // for (WorkSet::const_iterator f = Q.begin(); f != Q.end(); ++f) {
    //   // If f is in All workset, then it should be skipped.
    //   // But may be this is useless.
    //   if (All.find(*f) == All.end()) { continue; }
    //   slicers[*f]->calculateStaticSlice();
    // }
    // for (WorkSet::const_iterator f = Q.begin(); f != Q.end(); ++f) {
    //   if (All.find(*f) == All.end()) { continue; }
    //   emitToCalls(*f, std::inserter(tmp, tmp.end()));
    //   // errs() << "[+]tmp.size(): " << tmp.size() << "\n";
    //   emitToExits(*f, std::inserter(tmp, tmp.end()));
    //   // errs() << "[+]exits tmp.size(): " << tmp.size() << "\n";
    // }
  //   std::swap(tmp, Q);

  //   std::vector<const Function *> x(Q.begin(), Q.end());
  //   std::sort(x.begin(), x.end());
  //   x.erase(std::unique(x.begin(), x.end()), x.end());
  //   errs() << x.size() << "\n";

  //   if (x.size() != Q.size()) {
  //     Q.clear();
  //     Q.insert(x.begin(), x.end());
  //     All.insert(x.begin(), x.end());
  //   }
  // }

  std::vector<Rule *> toCheck(ruleWorklist);
  std::vector<Rule *> worklist(ruleWorklist);

  while (!worklist.empty()) {
    std::vector<Rule *> tmp;

    for (auto &w : worklist) {
      for (auto &c : w->getChildren()) {
        if (c->getType() == Constraint::RULE) {
          tmp.push_back((Rule *)c);
          toCheck.push_back((Rule *)c);
        }
      }
    }

    std::swap(worklist, tmp);
  }

  std::vector<Path *> paths;
  auto createPath = [&](const Instruction *call, const Instruction *inst,
                        Rule *rule, Path *parent = nullptr) {
    InsInfo *C_info = getInsInfo(inst);
    assert(C_info);

    PathElement *element = nullptr;
    Path *path = nullptr;
    if (parent) {
      path = parent;
      element = new PathElement(inst, inst);
      path->getLast()->setNext(element);
      element->setPrev(path->getLast());
    } else if (call) {
      path = new Path();
      PathElement *start = new PathElement(call, inst);
      element = new PathElement(inst, inst);
      path->setEntry(start);
      start->setNext(element);
      element->setPrev(start);
    } else {
      path = new Path();
      element = new PathElement(inst, inst);
      path->setEntry(element);
    }

    std::vector<Path *> p;
    std::mutex pathLock;
    if (C_info->backtrack(this, element, p, pathLock, *rule)) {
      pathLock.lock();
      if (std::find_if(p.begin(), p.end(), [path](const Path *other) {
            return *path == *other;
          }) == p.end()) {
        p.push_back(path);
      }
      pathLock.unlock();
    } else {
      delete (path);
    }
    std::sort(p.begin(), p.end());

    bool modified = false;
    do {
      modified = false;
      for (std::vector<Path *>::iterator i = p.begin();
           i != p.end() && !modified; ++i) {
        std::vector<Path *>::iterator j = i;
        std::advance(j, 1);
        for (; j != p.end(); ++j) {
          if (i == j)
            continue;
          if (**i == **j) {
            p.erase(j);
            modified = true;
            break;
          }
        }
      }
    } while (modified);

    rule->addPaths(p);
  };

  errs() << "====== Backtrack ======\n";
  for (std::vector<Rule *>::iterator rule = toCheck.begin();
       rule != toCheck.end(); ++rule) {
    for (auto &C : (*rule)->getInitialInstruction()) {
      errs() << (*rule)->getRuleTitle() << "\n";
      for (auto &C_pre : C.second) {
        createPath(C.first.first, C_pre.first, C_pre.second);
      }

      if ((*rule)->getParentRuleTitle().size()) {
        errs() << (*rule)->getRuleTitle() << "\n";
        for (auto &p : rules) {
          if (p->getRuleTitle() == (*rule)->getParentRuleTitle()) {
            for (auto &path : p->getPaths()) {
              if (path->getLast()->getElement() == C.first.first) {
                p->setDismissable(path);
                createPath(C.first.first, C.first.second, *rule,
                           new Path(*path));
              }
            }
          }
        }
      } else {
        createPath(C.first.first, C.first.second, *rule);
      }
    }
  }
  errs() << "Backtrack done\n";

  for (auto &rule : ruleWorklist) {
    rule->removeDismissablePaths();
    errs() << rule->getRuleTitle() << "\n";
    rule->checkRule();
  }

  std::vector<Rule *> checkRules(ruleWorklist);
  ruleWorklist.clear();
  for (auto &rule : checkRules) {
    for (auto &path : rule->getPaths()) {
      if (path->getLast()->getType() == PathElementBase::ConstAddressElement) {
        if (((ConstPathElement *)path->getLast())->shouldCreateNewCriterion()) {
          Rule *newRule = new Rule(*rule, path->getLast()->getElement());
          if (!addRule(newRule)) {
            delete newRule;
          }
        }
      }
    }
  }
}

void IntraDFA::computeSlice() {
  // while (ruleWorklist.size()) {
  ruleIteraton();
  // }
}

// Maybe we can develop a sliceFunction function.
// TODO if modified removeUndefs on functions which are found by rules
// callgraph.
bool IntraDFA::sliceModule() {
  bool modified = false;
  for (Slicers::iterator s = slicers.begin(); s != slicers.end(); ++s) {
    modified |= s->second->slice();
  }
  if (modified) {
    for (Module::iterator I = module.begin(), E = module.end(); I != E; ++I) {
      if (!I->isDeclaration()) {
        FunctionIntraDFA::removeUndefs(MP, *I);
      }
    }
  }

  return modified;
}

// TODO
bool IntraDFA::sliceFunction(Function *f) {
  if (slicers[f]->slice()) {
    if (!f->isDeclaration()) {
      FunctionIntraDFA::removeUndefs(MP, *f);
    }
  }
}

bool IntraDFA::addRule(Rule *rule) {
  if (std::find_if(rules.begin(), rules.end(), [&](Rule *other) {
        return *rule == *other;
      }) != rules.end()) {
    return false;
  }
  rules.push_back(rule);
  ruleWorklist.push_back(rule);
  return true;
}

// TODO: The rule function as the callie, to find the caller function as a
// initial function？
bool addCriterion(FunctionIntraDFA &fidfa, std::string functionName,
                  const Instruction *inst, uint64_t regNo, Rule &rule,
                  std::vector<Rule *> preconditions) {
  bool hadAsset = false;
  DetectParametersPass::UserSet_t pre =
      DetectParametersPass::getRegisterValuesBeforeCall(regNo, inst, true);
  for (auto &p_it : pre) {
    Rule::InstructionRuleList_t preconditionInstructions;

    for (auto &preCond : preconditions) {
      for (auto &preCrit : preCond->getCriterions()) {
        if (preCrit.second.first.getFunctionName() != functionName) {
          continue;
          llvm_unreachable("Precondition has to be for the same function");
        }
        DetectParametersPass::UserSet_t prePreCond =
            DetectParametersPass::getRegisterValuesBeforeCall(
                preCrit.second.first.getRegNo(), (Instruction *)inst, true);
        for (auto &prePreCond_it : prePreCond) {
          const Instruction *prePreInst =
              dyn_cast<const Instruction>(prePreCond_it);
          Rule::InstructionRule_t instRule(prePreInst, (Rule *)preCrit.first);
          preconditionInstructions.push_back(instRule);
          fidfa.addInitialCriterion(inst,
                                    ptr::PointsToSets::Pointee(prePreInst, -1));
        }
      }
    }

    fidfa.addInitialCriterion(inst, ptr::PointsToSets::Pointee(p_it, -1));
    rule.addInitialInstruction(inst, dyn_cast<const Instruction>(p_it),
                               preconditionInstructions);
    hadAsset = true;
  }
  return hadAsset;
};

void IntraDFA::findInitialCriterions() {
  bool hadAsset = false;
  for (auto &rule : ruleWorklist) {
    for (auto &criterion : rule->getCriterions()) {
      SimpleCallGraph::InstructionSet_t callerInstructions =
          ptr::getSimpleCallGraph().getCallers(
              criterion.second.first.getFunctionName());
      for (auto &inst : callerInstructions) {
        const Function *f = inst->getParent()->getParent();
        errs() << f->getName() << "\n";
        if (f->isDeclaration() || memoryManStuff(&*f)) {
          continue;
        }
        FunctionIntraDFA *fidfa = slicers[f];
        hadAsset =
            addCriterion(*fidfa, inst->getParent()->getParent()->getName(),
                         inst, criterion.second.first.getRegNo(),
                         *(Rule *)criterion.first, criterion.second.second);
        errs() << "Found caller to " << criterion.second.first.getFunctionName()
               << "\n";

        if (hadAsset) {
          initFuncs.push_back(f);
          fidfa->initializeInfos();
        }
      }
    }
  }
}

void IntraDFA::addInitialSlicingCriterion(const Instruction *C) {
  InitialCriterions.insert(C);
}

InsInfo *IntraDFA::getInsInfo(const Instruction *I) {
  if (!I) {
    return nullptr;
  }

  const Function *f = I->getParent()->getParent();
  FunctionIntraDFA *fidfa = slicers[f];

  if (!fidfa->isInitialized()) {
    return nullptr;
  } else {
    return fidfa->getInsInfo(I);
  }
}
} // namespace dfa
} // namespace llvm

char FunctionSlicer::ID = 0;
static RegisterPass<FunctionSlicer> X("slice-intra", "view CFG of function", false,
                              true);
static RegisterAnalysisGroup<FunctionSlicer> Y(X);

bool FunctionSlicer::runOnModule(Module &M) {
  using llvm::slicing::Constraint;
  using llvm::slicing::Parameter;
  using llvm::slicing::Rule;
  std::vector<Rule *> rules = llvm::slicing::parseRules();

  for (auto &r : rules) {
    if (r->getParentRuleTitle().size()) {
      for (auto &r2 : rules) {
        if (r2->getRuleTitle() == r->getParentRuleTitle()) {
          r->setParentRule(r2);
        }
      }
    }
  }

  ptr::PointsToSets *PS = new ptr::PointsToSets();
  ptr::ProgramStructure P(M, rules);
  computePointsToSets(P, *PS);

  callgraph::Callgraph CG(M, *PS);
  mods::Modifies MOD;
  mods::ProgramStructure P1(M, *PS);
  computeModifies(P1, CG, *PS, MOD);


  dfa::IntraDFA DFA(this, M, (*PS), CG, MOD, rules);
  DFA.computeSlice();

  free(PS);
  bool s = DFA.sliceModule();

  raw_fd_ostream *report_stream = nullptr;
  if (ReportFilename.length()) {
    std::error_code EC;

    report_stream = new raw_fd_ostream(ReportFilename, EC, sys::fs::F_None);

    if (EC) {
      errs() << EC.message() << '\n';
    }
  }

  llvm::slicing::HTMLReportPrinter reportPrinter(report_stream ? *report_stream
                                                               : nulls());
  for (auto &rule : DFA.getRules()) {
    errs() << "Print results of \"" << rule->getRuleTitle() << "\"\n";
    const Rule::CompletePathResultList_t &results = rule->getResults();
    errs() << results.size() << " paths\n";
    reportPrinter.addResults(rule, results);
  }
  reportPrinter.close();

  if (report_stream) {
    report_stream->close();
    delete (report_stream);
  }
  return s;
}

void FunctionSlicer::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<PostDominatorTree>();
  AU.addRequired<PostDominanceFrontier>();
}