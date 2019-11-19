// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.

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
#include "../Backtrack/ScanRule.h"
#include "../Backtrack/Rule.h"
#include "../Callgraph/Callgraph.h"
#include "../Modifies/Modifies.h"
#include "../PointsTo/PointsTo.h"
#include "../Slicing/FunctionStaticSlicer.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/ScanMethod/ScanMethod.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"

#define DEBUG_TYPE "slicer"
// #define DUMP_CALLS

using namespace llvm;

static cl::opt<std::string>
    ScanReportFilename("sr", cl::desc("Path to HTML scan method report output file"),
                   cl::value_desc("scan_report"));


namespace llvm {
namespace slicing {



class ScanStaticSlicer : public InsInfoProvider {
public:
  typedef std::map<llvm::Function const *, FunctionStaticSlicer *> Slicers;
  typedef std::multimap<llvm::Function const *, llvm::CallInst const *>
      FuncsToCalls;
  typedef std::multimap<llvm::CallInst const *, llvm::Function const *>
      CallsToFuncs;

  ScanStaticSlicer(ModulePass *MP, Module &M, const ptr::PointsToSets &PS,
               const callgraph::Callgraph &CG, const mods::Modifies &MOD,
               std::vector<Rule *> rules);

  ~ScanStaticSlicer();

  void computeSlice();
  void ruleIteration();

  virtual void addInitialSlicingCriterion(const Instruction *C);

  virtual InsInfo *getInsInfo(const Instruction *I);


  bool addRule(Rule *rule);
  const std::vector<Rule *> getRules() const { return rules; }

protected:
  typedef llvm::SmallVector<const llvm::Function *, 20> InitFuns;

  legacy::PassManager *PM;
  DetectParametersPass *DPP;
  const ptr::PointsToSets &PS;
  const mods::Modifies &MOD;

  std::vector<Rule *> rules;
  std::vector<Rule *> ruleWorklist;

  void buildDicts(const ptr::PointsToSets &PS, const CallInst *c);
  void buildDicts(const ptr::PointsToSets &PS);

  void findInitialCriterions();


  void runFSS(Function &F, const ptr::PointsToSets &PS,
              const callgraph::Callgraph &CG, const mods::Modifies &MOD);

  ModulePass *MP;
  Module &module;
  Slicers slicers;
  std::mutex slicersLock;
  InitFuns initFuns;
  FuncsToCalls funcsToCalls;
  CallsToFuncs callsToFuncs;

  std::set<const Instruction *> InitialCriterions;
};

void ScanStaticSlicer::addInitialSlicingCriterion(const Instruction *C){

}
InsInfo *ScanStaticSlicer::getInsInfo(const Instruction *I){
  return nullptr;
}


bool ScanStaticSlicer::addRule(Rule *rule) {
  if (std::find_if(rules.begin(), rules.end(),
                   [&](Rule *other) { return *rule == *other; }) != rules.end())
    return false;
  rules.push_back(rule);
  ruleWorklist.push_back(rule);
  return true;
}

ScanStaticSlicer::~ScanStaticSlicer() {
  for (Slicers::const_iterator I = slicers.begin(), E = slicers.end(); I != E;
       ++I)
    delete I->second;
}

ScanStaticSlicer::ScanStaticSlicer(ModulePass *MP, Module &M,
                           const ptr::PointsToSets &PS,
                           const callgraph::Callgraph &CG,
                           const mods::Modifies &MOD, std::vector<Rule *> rules)
    : PS(PS), MOD(MOD), MP(MP), module(M), slicers(), initFuns(),
      funcsToCalls(), callsToFuncs() {
  for (auto &rule : rules) {
    addRule(rule);
  }
  for (Module::iterator f = M.begin(); f != M.end(); ++f)
    if (!f->isDeclaration() && !memoryManStuff(&*f))
      runFSS(*f, PS, CG, MOD);
  buildDicts(PS);
  PM = new legacy::PassManager();
  DPP = new DetectParametersPass();
  PM->add(DPP);

  PM->run(M);
}

void ScanStaticSlicer::runFSS(Function &F, const ptr::PointsToSets &PS,
                          const callgraph::Callgraph &CG,
                          const mods::Modifies &MOD) {

  FunctionStaticSlicer *FSS = new FunctionStaticSlicer(F, MP, PS, MOD, this);

  slicers.insert(Slicers::value_type(&F, FSS));
}

void ScanStaticSlicer::buildDicts(const ptr::PointsToSets &PS, const CallInst *c) {
  typedef std::vector<const Function *> FunCon;
  FunCon G;
  getCalledFunctions(c, PS, std::back_inserter(G));

  for (FunCon::const_iterator I = G.begin(), E = G.end(); I != E; ++I) {
    const Function *h = *I;

    if (!memoryManStuff(h) && !h->isDeclaration()) {
      funcsToCalls.insert(std::make_pair(h, c));
      callsToFuncs.insert(std::make_pair(c, h));
    }
  }
}

void ScanStaticSlicer::buildDicts(const ptr::PointsToSets &PS) {
  for (Module::const_iterator f = module.begin(); f != module.end(); ++f)
    if (!f->isDeclaration() && !memoryManStuff(&*f))
      for (const_inst_iterator I = inst_begin(*f), E = inst_end(*f); I != E;
           ++I)
        if (const CallInst *c = dyn_cast<CallInst>(&*I)) {
          if (isInlineAssembly(c)) {
            errs() << "ERROR: Inline assembler detected in " << f->getName()
                   << ", skipping\n";
            continue;
          }

          buildDicts(PS, c);
        }
}

void ScanStaticSlicer::ruleIteration() {
  findInitialCriterions();

  
  //        typedef SmallVector<const Function *, 20> WorkSet;
  typedef std::set<const Function *> WorkSet;
  //        WorkSet Q(initFuns);
  WorkSet Q;
  for (auto &i : initFuns) {
    Q.insert(i);
  }

  errs() << "Found " << initFuns.size() << " initial criterions\n";

  initFuns.clear();
  
}

void ScanStaticSlicer::computeSlice() {
  while (ruleWorklist.size()) {
    ruleIteration();
  }
}




void ScanStaticSlicer::findInitialCriterions() {
  for (Module::iterator f = module.begin(); f != module.end(); ++f) {
    if (!f->isDeclaration() && !memoryManStuff(&*f)) {
      FunctionStaticSlicer *FSS = slicers[f];
      bool hadAssert = slicing::findInitialCriterion(*f, *FSS, ruleWorklist);

      if (hadAssert) {
        initFuns.push_back(f);
        FSS->initializeInfos();
      }
    }
  }
}




} // namespace slicing
} // namespace llvm

char ScanMethod::ID = 0; /* pass id */

// https://llvm.org/docs/WritingAnLLVMPass.html#the-runonmodule-method
bool ScanMethod::runOnModule(Module &M) {
  errs() << "[+]Start ScanMethod Pass"
        << "\n";

  using llvm::slicing::Constraint;
  using llvm::slicing::Parameter;
  using llvm::slicing::Rule;
  std::vector<Rule*> c_rule;
  std::vector<Rule*> objc_rule; 
  llvm::slicing::parseScanRules(&c_rule, &objc_rule);

  ptr::PointsToSets *PS = new ptr::PointsToSets();
  {
    ptr::ProgramStructure P(M);
    errs() << "[i]first ProgramStructure\n";
    computePointsToSets(P, *PS, c_rule);
  }

  callgraph::Callgraph CG(M, *PS);
  /*
  dont know weather the cg works write ;
   */
  for (auto &rule : c_rule) {
    for (auto &criterion : rule->getCriterions()) {
      std::string function_name = criterion.second.first.getFunctionName();
      Function* tmp_fun = M.getFunction(function_name);
      llvm::callgraph::Callgraph::range_iterator callees_range = CG.directCallees(tmp_fun);
      for(auto call_pair = callees_range.first; call_pair!= callees_range.second; call_pair++){
        errs()<<"fun : "<<call_pair->second->getName()<<" call fun: "<<function_name<<"\n";
      }
    }
  }
  for(auto tmp_fun = M.begin();tmp_fun != M.end(); tmp_fun++){
    for(auto tmp_bb = tmp_fun->begin(); tmp_bb != tmp_fun->end(); tmp_bb++){
      for(auto tmp_inst = tmp_bb->begin(); tmp_inst!=tmp_bb->end();tmp_inst++){
        if(tmp_inst->getOpcode() == Instruction::Call){
          SimpleCallGraph::FunctionSet_t calledFunctions = ptr::getSimpleCallGraph().getCalled(&*tmp_inst);
          CallInst* tmp_call_inst = dyn_cast<CallInst>(tmp_inst);
          //if(tmp_call_inst->getCalledFunction()->getName()!)
        }
      }
    }
  }

  mods::Modifies MOD;
  {
    mods::ProgramStructure P1(M, *PS);
    errs() << "[i]second programStructure\n";
    computeModifies(P1, CG, *PS, MOD);
  }
  errs() << "done\n";
  /* 
  for (auto &r : rules) {
    if (r->getParentRuleTitle().size()) {
      for (auto &r2 : rules) {
        if (r2->getRuleTitle() == r->getParentRuleTitle()) {
          r->setParentRule(r2);
        }
      }
    }
  }
  */

  slicing::ScanStaticSlicer SSS(this, M, (*PS), CG, MOD, objc_rule);
  SSS.computeSlice();

  free(PS);
  //bool s = SSS.sliceModule();

  raw_fd_ostream *report_stream = nullptr;
  if (ScanReportFilename.length()) {
    std::error_code EC;

    report_stream = new raw_fd_ostream(ScanReportFilename, EC, sys::fs::F_None);

    if (EC) {
      errs() << EC.message() << '\n';
    }
  }

  llvm::slicing::HTMLReportPrinter reportPrinter(report_stream ? *report_stream
                                                               : nulls());
  for (auto &rule : SSS.getRules()) {
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
  return true;
}

