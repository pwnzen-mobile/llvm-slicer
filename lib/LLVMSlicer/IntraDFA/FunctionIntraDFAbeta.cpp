#include "llvm/IntraDFA/FunctionIntraDFAbeta.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"
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
#include "../Languages/LLVMSupport.h"
#include "../Modifies/Modifies.h"
#include "../PointsTo/PointsTo.h"
#include "./FunctionIntraDFAbeta.h"

using namespace llvm;
static cl::opt<std::string>
    ReportFilename("r", cl::desc("Path to HTML report output file"),
                   cl::value_desc("report"));

namespace llvm {
namespace beta {
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

class DFA : public InsInfoProvider {
public:
  typedef std::map<llvm::Function const *, FunctionIntraDFA *> Slicers;
  typedef std::multimap<llvm::Function const *, llvm::CallInst const *>
      FuncsToCalls;
  typedef std::multimap<llvm::CallInst const *, llvm::Function const *>
      CallsToFuncs;

  DFA(ModulePass *MP, Module &M, const ptr::PointsToSets &PS,
      const callgraph::Callgraph &CG, const mods::Modifies &MOD,
      std::vector<slicing::Rule *> rules);
  ~DFA();

  void ruleIteration();
  // virtual void addInitialCriterion(const Instruction *c);
  virtual void addInitialSlicingCriterion(const Instruction *C);
  virtual InsInfo *getInsInfo(const Instruction *c);
  bool addRule(slicing::Rule *rule);
  const std::vector<slicing::Rule *> getRules() const { return rules; }

private:
  typedef llvm::SmallVector<const llvm::Function *, 20> InitFuncs;
  Module &module;
  legacy::PassManager *PM;
  const mods::Modifies &MOD;
  ModulePass *MP;
  DetectParametersPass *DPP;
  const ptr::PointsToSets &PS;
  Slicers slicers;
  std::vector<slicing::Rule *> rules;
  std::vector<slicing::Rule *> ruleWorklist;
  InitFuncs initFuncs;
  FuncsToCalls funcsToCalls;
  CallsToFuncs callsToFuncs;
  std::set<const Instruction *> InitialCriterions;

  void emitToCalls(llvm::Function const *const f);
  void emitToExits(llvm::Function const *const f);

  void findInitialCriterations();
  void buildDicts(const ptr::PointsToSets &PS, const CallInst *c);
  void runDFA();
};

// void DFA::buildDicts(const ptr::PointsToSets &PS, const CallInst *c) {
//   typedef std::vector<const Function *> FunV;
//   FunV G;
//   getCalledFunctions(c, PS, std::back_inserter(G));

//   for (FunV::const_iterator I = G.begin(), E = G.end(); I != E; ++I) {
//     const Function *f = *I;
//     if (!memoryManStuff(f) && !f->isDeclaration()) {
//       funcsToCalls.insert(std::make_pair(f, c));
//       callsToFuncs.insert(std::make_pair(c, f));
//     }
//   }
// }

bool DFA::addRule(slicing::Rule *rule) {
  if (std::find_if(rules.begin(), rules.end(), [&](slicing::Rule *other) {
        return *rule == *other;
      }) != rules.end()) {
    return false;
  }
  rules.push_back(rule);
  ruleWorklist.push_back(rule);
  return true;
}

InsInfo *DFA::getInsInfo(const Instruction *I) {
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

DFA::DFA(ModulePass *MP, Module &M, const ptr::PointsToSets &PS,
         const callgraph::Callgraph &CG, const mods::Modifies &MOD,
         std::vector<slicing::Rule *> rules)
    : PS(PS), MOD(MOD), MP(MP), module(M), initFuncs(), funcsToCalls(),
      callsToFuncs() {
  for (auto &rule : rules) {
    addRule(rule);
  }

  PM = new legacy::PassManager();
  DPP = new DetectParametersPass();
  PM->add(DPP);
  PM->run(M);
}

DFA::~DFA() {}

void DFA::addInitialSlicingCriterion(const Instruction *C) {
  InitialCriterions.insert(C);
}

void DFA::findInitialCriterations() {
  for (Module::iterator f = module.begin(); f != module.end(); ++f) {
    if (!f->isDeclaration() && !memoryManStuff(&*f)) {
      FunctionIntraDFA *FIDFA =
          new beta::FunctionIntraDFA(*f, MP, PS, MOD, this);
      slicers.insert(Slicers::value_type(&*f, FIDFA));
      for (inst_iterator I = inst_begin(*f), E = inst_end(*f); I != E; ++I) {
        bool hadAssert = beta::findInitialCriterion(I, *FIDFA, ruleWorklist);
        if (hadAssert) {
          initFuncs.push_back(f);
          FIDFA->initializeInfos();
        }
      }
    }
  }
  errs() << "Found " << initFuncs.size() << " initial criterions\n";
}

void DFA::emitToCalls(const Function *f) {
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
      // DEBUG(errs() << "Not modified: "; rem.first->dump());
      R.erase(rem);
    }

    if (!R.size()) {
      // DEBUG(errs() << "No relevant variables in scope " << f->getName()
                  //  << "\n");
      continue;
    }

    FIDFA->initializeInfos();
    InsInfo *CallInfo = FIDFA->getInsInfo(CI);

    if (FIDFA->addCriterion(CI, R.begin(), R.end(), this, rcSources, RCInc,
                            !FIDFA->shouldSkipAssert(CI))) {
      FIDFA->addCriterion(CI, FIDFA->REF_begin(CI), FIDFA->REF_end(CI));
      calls.insert(c->second->getParent()->getParent()->getName().str());
    }

    for (auto &structInfo_it : structSliceInfos) {
      for (auto &ssi_it : structInfo_it.second) {
        CallInfo->addRCStruct(structInfo_it.first, ssi_it);
      }
    }
  }
}


void DFA::emitToExits(const Function *f) {
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

void DFA::ruleIteration() {
  findInitialCriterations();

  for (auto &f : initFuncs) {
    slicers[f]->calculateStaticSlice();
    emitToCalls(f);
    emitToExits(f);
  }

  std::vector<slicing::Rule *> toCheck(ruleWorklist);
  std::vector<slicing::Rule *> worklist(ruleWorklist);
  while (!worklist.empty()) {
    std::vector<slicing::Rule *> tmp;

    for (auto &w : worklist) {
      for (auto &c : w->getChildren()) {
        if (c->getType() == slicing::Constraint::RULE) {
          tmp.push_back((slicing::Rule *)c);
          toCheck.push_back((slicing::Rule *)c);
        }
      }
    }

    std::swap(worklist, tmp);
  }

  std::vector<slicing::Path *> paths;
  auto createPath = [&](const Instruction *call, const Instruction *inst,
                        slicing::Rule *rule, slicing::Path *parent = nullptr) {
    InsInfo *C_info = getInsInfo(inst);
    assert(C_info);

    slicing::PathElement *element = nullptr;
    slicing::Path *path = nullptr;
    if (parent) {
      path = parent;
      element = new slicing::PathElement(inst, inst);
      path->getLast()->setNext(element);
      element->setPrev(path->getLast());
    } else if (call) {
      path = new slicing::Path();
      slicing::PathElement *start = new slicing::PathElement(call, inst);
      element = new slicing::PathElement(inst, inst);
      path->setEntry(start);
      start->setNext(element);
      element->setPrev(start);
    } else {
      path = new slicing::Path();
      element = new slicing::PathElement(inst, inst);
      path->setEntry(element);
    }

    std::vector<slicing::Path *> p;
    std::mutex pathLock;
    if (C_info->backtrack(this, element, p, pathLock, *rule)) {
      pathLock.lock();
      if (std::find_if(p.begin(), p.end(), [path](const slicing::Path *other) {
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
      for (std::vector<slicing::Path *>::iterator i = p.begin();
           i != p.end() && !modified; ++i) {
        std::vector<slicing::Path *>::iterator j = i;
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
  for (std::vector<slicing::Rule *>::iterator rule = toCheck.begin();
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
                           new slicing::Path(*path));
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

  std::vector<slicing::Rule *> checkRules(ruleWorklist);
  ruleWorklist.clear();
  for (auto &rule : checkRules) {
    for (auto &path : rule->getPaths()) {
      if (path->getLast()->getType() ==
          slicing::PathElementBase::ConstAddressElement) {
        if (((slicing::ConstPathElement *)path->getLast())
                ->shouldCreateNewCriterion()) {
          slicing::Rule *newRule =
              new slicing::Rule(*rule, path->getLast()->getElement());
          if (!addRule(newRule)) {
            delete newRule;
          }
        }
      }
    }
  }
}
} // namespace beta
} // namespace llvm

char FunctionIntraDFAbeta::ID = 0;
static RegisterPass<FunctionIntraDFAbeta> X("intra-dfa", "view CFG of function",
                                            false, true);
static RegisterAnalysisGroup<FunctionIntraDFAbeta> Y(X);

bool FunctionIntraDFAbeta::runOnModule(Module &M) {
  using llvm::slicing::Constraint;
  using llvm::slicing::Parameter;
  using llvm::slicing::Rule;
  std::vector<Rule *> rules = llvm::slicing::parseRules();

  ptr::PointsToSets *PS = new ptr::PointsToSets();
  ptr::ProgramStructure P(M, rules);
  computePointsToSets(P, *PS);

  callgraph::Callgraph CG(M, *PS);
  mods::Modifies MOD;
  mods::ProgramStructure P1(M, *PS);
  computeModifies(P1, CG, *PS, MOD);


  for (auto &r : rules) {
    if (r->getParentRuleTitle().size()) {
      for (auto &r2 : rules) {
        if (r2->getRuleTitle() == r->getParentRuleTitle()) {
          r->setParentRule(r2);
        }
      }
    }
  }

  beta::DFA dfa(this, M, (*PS), CG, MOD, rules);
  dfa.ruleIteration();
  free(PS);

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
  for (auto &rule : dfa.getRules()) {
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
  return false;
}

void FunctionIntraDFAbeta::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<PostDominatorTree>();
  AU.addRequired<PostDominanceFrontier>();
}