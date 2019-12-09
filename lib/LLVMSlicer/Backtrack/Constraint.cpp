#include "Constraint.h"
#include "Rule.h"
#include <PointsTo/PointsTo.h>
#include <llvm/ADT/StringExtras.h>
#include <sstream>

using namespace llvm;
using namespace slicing;

cl::opt<bool>
    PrintSameUseDef("print-same-usedef-only",
                    cl::desc("Paths with same use-def are only printed once"),
                    cl::init(false), cl::Hidden);

Message::Message(Path *path, bool isPrecondition)
    : isPrecondition(isPrecondition), path(path) {}

void Message::dump() {
  if (isPrecondition) {
    errs() << "Precondition not always fulfilled\n";
  }
  path->dump(false);
}

Parameter::Parameter(std::string functionName, uint64_t regNo,
                     ParameterType parameterType)
    : functionName(functionName), regNo(regNo), parameterType(parameterType) {}

std::string Parameter::getFunctionName() const { return functionName; }

uint64_t Parameter::getRegNo() const { return regNo; }

Parameter::ParameterType Parameter::getParameterType() const {
  return parameterType;
}

//------------------------------------------
// Constraint
//------------------------------------------

Constraint::Constraint(ConstraintType constraintType)
    : constraintType(constraintType) {}

void Constraint::addConstraint(const Constraint *constraint) {
  children.push_back(constraint);
}

Constraint::Type Constraint::getType() const { return CONSTRAINT; }

const Constraint::ConstraintList_t &Constraint::getChildren() const {
  return children;
}

Constraint::ConstraintType Constraint::getConstraintType() const {
  return constraintType;
}

//------------------------------------------
// ChainedConstraint
//------------------------------------------

ChainConstraint::ChainConstraint(ConstraintType constraintType,
                                 ChainType chainType)
    : Constraint(constraintType), chainType(chainType) {}

// 0 => ERROR; 2 => UNKNOWN; 3 => VALID
int ChainConstraint::checkConstraint(PathElementBase *pathElement) const {
  int result = 0;
  switch (chainType) {
  case AND: {
    result = 3;
    for (auto &child : children) {
      result &= child->checkConstraint(pathElement);
    }
    break;
  }
  case OR: {
    for (auto &child : children) {
      result |= child->checkConstraint(pathElement);
    }
    break;
  }
  case NOT_AND: {
    result = 3;
    for (auto &child : children) {
      result &= ~child->checkConstraint(pathElement);
    }
    break;
  }
  default:
    llvm_unreachable("");
  }
  return result == 1 ? 2 : result;
}

bool ChainConstraint::shouldStop(PathElementBase *pathElement) const {
  bool result = false;
  switch (chainType) {
  // FIXME: we just "NOT" the result when check constraint, so let it the same with "OR".
  case NOT_AND:
  case OR: {
    for (auto &child : children) {
      result |= child->shouldStop(pathElement);
    }
    break;
  }
  // case NOT_AND: {
  //   // TODO: how to handle this, we can't stop always when we NOT find
  //   // something...
  //   result = false;
  //   break;
  // }
  default:
    llvm_unreachable("");
  }
  return result;
}

//------------------------------------------
// ConstConstraint
//------------------------------------------

ConstConstraint::ConstConstraint(
    Compare compare, ConstraintType constraintType, uint64_t value = 0,
    std::string strvalue = "",
    std::vector<std::string> strings = std::vector<std::string>())
    : compare(compare), Constraint(constraintType), value(value),
      strvalue(strvalue), strings(strings) {}

ConstConstraint::ConstConstraint(
    Compare compare, ConstraintType constraintType, uint64_t value = 0,
    std::set<std::map<std::string, int>> intDicts = std::set<std::map<std::string, int>>(), std::set<std::map<std::string, std::string>> strDicts = std::set<std::map<std::string, std::string>>())
    : compare(compare), Constraint(constraintType), value(value),
      intDicts(intDicts), strDicts(strDicts) {}

// 0 => ERROR; 2 => UNKNOWN; 3 => VALID
int ConstConstraint::checkConstraint(PathElementBase *pathElement) const {
  const Instruction *inst =
      dyn_cast<const Instruction>(pathElement->getElement());
  if (inst) {
    if (inst->getOpcode() == Instruction::Store) {
      const ConstantInt *constInt =
          dyn_cast<const ConstantInt>(inst->getOperand(0));
      // const ConstantDataSequential *constStr = dyn_cast<const
      // ConstantDataSequential>(inst->getOperand(0));
      switch (compare) {
      case EQUAL: {
        if (constInt) {
          if (constInt->getZExtValue() == value) {
            return 3;
          } else {
            return 0;
          }
        } else {
          return 2;
        }
        break;
      }
      case GREATER: {
        if (constInt) {
          if (constInt->getZExtValue() > value) {
            return 3;
          } else {
            return 0; 
          }
        } else {
          return 2;
        }
        break;
      }
      case LOREQ: {
        if (constInt){
          if ((constInt->getZExtValue() | value) == value) {
            return 3;
          }
          else {
            return 0;
          }
        } else {
          return 2;
        }
        break;
      }
      case LORNEQ: {
        if (constInt){
          if ((constInt->getZExtValue() & value) != value) {
            return 3;
          }
          else {
            return 0;
          }
        } else {
          return 2;
        }
        break;
      }
      case IN:
      case NOTIN: {
        // constInt is a address, get value from constInt whether it's a const
        // string or type string.
        if (constInt) {
          StringRef ref;
          uint64_t addr = constInt->getZExtValue();
          if (ptr::getAndersen()->getMachO().isCFString(addr) ||
              ptr::getAndersen()->getMachO().isCString(addr)) {
            ref = ptr::getAndersen()->getMachO().getString(addr);
          } else if (ptr::getAndersen()->getMachO().isClassRef(addr)) {
            ptr::getAndersen()->getMachO().getClass(addr, ref);
          } else if (ptr::getAndersen()->getMachO().isData(addr)) {
            ptr::getAndersen()->getMachO().getData(addr, ref);
          }
          errs() << "[+]ref.data(): " << ref.data() << "\n";
          if (find(strings.begin(), strings.end(), ref.data()) !=
              strings.end()) {
            if (compare == IN)
              return 3;
            else if (compare == NOTIN)
              return 0;
          } else {
            if (compare == IN)
              return 0;
            if (compare == NOTIN)
              return 3;
          }
        } else {
          return 2;
        }
        break;
      }
      case EXITS: {
        // TODO
        
      }
      case ANY: {
        if (constInt) {
          return 3;
        } else {
          return 2;
        }
      }
      default:
        llvm_unreachable("");
      }
    }
  } else if (const ConstantInt *constAddress =
                 dyn_cast<const ConstantInt>(pathElement->getElement())) {
    uint64_t width = pathElement->getParent()->getShortestLoad();
    uint64_t value = 0;
    switch (width) {
    case 32: {
      value = ptr::getAndersen()->getMachO().getRAWData<uint32_t>(
          constAddress->getZExtValue());
      break;
    }
    case 64: {
      value = ptr::getAndersen()->getMachO().getRAWData<uint64_t>(
          constAddress->getZExtValue());
      break;
    }
    /*
      add by -death 
     */
    case 8: {
      value = ptr::getAndersen()->getMachO().getRAWData<uint8_t>(
          constAddress->getZExtValue());
      break; 
    }
    case 16: {
      value = ptr::getAndersen()->getMachO().getRAWData<uint8_t>(
          constAddress->getZExtValue());
      break; 
    }
    /*
      add by -death end 
     */
    default:
      llvm_unreachable("");
    }
    if (!value) {
      return 2;
    }
    // errs() << "[+]width: , value: " << width << " " << value << "\n";`

    if (compare == EQUAL) {
      if (value == this->value) {
        return 3;
      } else {
        return 0;
      }
    } else if (compare == GREATER) {
      if (value > this->value) {
        return 3;
      } else {
        return 0;
      }
    } else if (compare == LORNEQ) {
      if ((value & this->value) != this->value) {
        return 3;
      } else {
        return 0;
      }
    } else if (compare == ANY) {
      return 3;
    } else if (compare == IN || compare == NOTIN) {
      // constInt is a address, get value from constInt whether it's a const
      // string or type string.
      uint64_t constInt = value;
      StringRef ref;
      uint64_t addr = value;
      if (ptr::getAndersen()->getMachO().isCFString(addr) ||
          ptr::getAndersen()->getMachO().isCString(addr)) {
        ref = ptr::getAndersen()->getMachO().getString(addr);
      } else if (ptr::getAndersen()->getMachO().isClassRef(addr)) {
        ptr::getAndersen()->getMachO().getClass(addr, ref);
      } else if (ptr::getAndersen()->getMachO().isData(addr)) {
        ptr::getAndersen()->getMachO().getData(addr, ref);
      }
      if (find(strings.begin(), strings.end(), ref.data()) != strings.end()) {
        if (compare == IN)
          return 3;
        else if (compare == NOTIN)
          return 0;
      }
    } else {
      if (compare == IN)
        return 0;
      else if (compare == NOTIN)
        return 3;
    }
  } else {
    llvm_unreachable("");
  }

  return 2;
}

bool ConstConstraint::shouldStop(PathElementBase *pathElement) const {
  if (const Instruction *inst =
          dyn_cast<const Instruction>(pathElement->getElement())) {
    if (inst->getOpcode() == Instruction::Store) {
      if (dyn_cast<const ConstantInt>(inst->getOperand(0))) {
        return true;
      }
    }
  }
  return false;
}

//------------------------------------------
// Rule
//------------------------------------------

Rule::Rule(std::string ruleTitle, ConstraintType constraintType,
           ChainType chainType)
    : ChainConstraint(constraintType, chainType), ruleTitle(ruleTitle) {}

Rule::Rule(const Rule &base, const llvm::Value *criterion)
    : ChainConstraint(base.constraintType, base.chainType),
      relevantLocation(criterion) {
  // std::stringstream ss;
  // ss << "Write to 0x";
  // ss << utohexstr(((ConstantInt *)criterion)->getZExtValue());
  // ruleTitle = ss.str();
  for (auto user : criterion->users()) {
    std::vector<const Value *> ptsToSet;
    ptr::getAndersen()->getPointsToSet(user, ptsToSet);
    for (auto &p : ptsToSet) {
      relevantVariables.push_back(p);
    }
    // They point all to the same location, thus we can stop here
    break;
  }
}

void Rule::addInitialInstruction(
    const Instruction *callInst, const Instruction *paramInst,
    InstructionRuleList_t preconditionInstruction) {
  //    if (std::find(initialInstructions.begin(), initialInstructions.end(),
  //    inst) != initialInstructions.end())
  //        return;
  initialInstructions.push_back(InitialInstructionPair_t(
      std::pair<const Instruction *, const Instruction *>(callInst, paramInst),
      preconditionInstruction));
}

const Rule::InitialInstructionList_t &Rule::getInitialInstruction() const {
  return initialInstructions;
}

int Rule::checkConstraint(PathElementBase *pathElement) const {
  return ChainConstraint::checkConstraint(pathElement);
}

bool Rule::shouldStop(PathElementBase *pathElement) const {
  if (children.size() == 0)
    return false;

  bool result = false;
  if (chainType == ChainConstraint::AND)
    result = true;
  for (auto &c : children) {
    bool c_r = c->shouldStop(pathElement);
    switch (chainType) {
    case ChainConstraint::AND: {
      result &= c_r;
      break;
    }
    case ChainConstraint::OR: {
      result |= c_r;
      break;
    }
    default:
      llvm_unreachable("");
    }
  }
  return result;
}

bool Rule::dismissPath(PathElementBase *pathElement) const {
  bool dismiss = false;
  if (const CallInst *callInst =
          dyn_cast<const CallInst>(pathElement->getElement())) {
    for (auto &calledFunction : ptr::getSimpleCallGraph().getCalled(callInst)) {
      if (calledFunction == "CC_SHA256_Init") {
        dismiss = true;
      } else {
        return false;
      }
    }
    return dismiss;
  }
  return false;
}

void Rule::addCriterion(Parameter parameter,
                        std::vector<Rule *> preconditions) {
  criterions.push_back(Criterion_t(parameter, preconditions));
}

Rule::RuleCriterionList_t Rule::getCriterions() const {
  RuleCriterionList_t ruleCriterionList;

  for (auto &c : criterions) {
    ruleCriterionList.push_back(RuleCriterion_t(this, c));
  }

  for (auto &c : children) {
    if (c->getType() == RULE) {
      RuleCriterionList_t cl = ((const Rule *)c)->getCriterions();
      ruleCriterionList.insert(ruleCriterionList.end(), cl.begin(), cl.end());
    }
  }

  return ruleCriterionList;
}

void Rule::addConstraint(const Constraint *constraint) {
  if (constraint->getConstraintType() == PRECONDITION) {
    if (children.size() > 0) {
      llvm_unreachable("only a single precondition may be added");
    }
    if (getConstraintType() != PRECONDITION && constraint->getType() != RULE) {
      llvm_unreachable(
          "The rule has to be a precondition if a constraint is one.");
    }
  }
  Constraint::addConstraint(constraint);
}

bool Rule::useParentPath(Path *path) { return false; }

Constraint::Type Rule::getType() const { return RULE; }

bool Rule::preconditions() const {
  bool cond = false;
  if (getConstraintType() == PRECONDITION) {
    for (auto &path : paths) {
      cond |= checkConstraint(path->getLast());
    }
  } else {
    cond = true;
  }
  return cond;
}

bool Rule::checkRule() {
  if (initialInstructions.size() && paths.size() == 0) {
    errs() << "ERROR: No paths found! " << ruleTitle << "\n";
  }
  checkedPaths = true;
  for (auto &path : paths) {
    // path->dump();
    if (!path->getEntry()->getNext())
      continue;
    const Instruction *first =
        dyn_cast<const Instruction>(path->getEntry()->getElement());
    const Instruction *pathStart =
        first->getOpcode() == Instruction::Call
            ? dyn_cast<const Instruction>(
                  path->getEntry()->getNext()->getElement())
            : dyn_cast<const Instruction>(path->getEntry()->getElement());
    if (!pathStart) {
      continue;
    }

    //        errs() << "PATHDUMP\n";
    //        path->dump();
    //        errs() << "--------\n";

    InitialInstructionPair_t initIns;

    if (parentRuleTitle.size()) {
      for (auto &x : parentRule->initialInstructions) {
        if (x.first.second == pathStart) {
          initIns = x;
        }
      }
    } else {
      for (auto &x : initialInstructions) {
        if (x.first.second == pathStart) {
          initIns = x;
        }
      }
    }

    //        for (auto &initIns : initialInstructions) {
    if (initIns.first.second == pathStart ||
        (parentRuleTitle.size() && path->contains(initIns.first.second))) {
      Result result = VALID;
      bool hasPrecond = false;
      bool precond = false;
      MessageList_t errorMessages;

      PrecondResultList_t preConditionResults;
      for (auto &preCond : initIns.second) {
        for (auto &p : preCond.second->getPaths(preCond.first)) {
          // p->dump();
          hasPrecond = true;
          int result = preCond.second->checkRule(p);
          PrecondResult_t preResult;
          std::get<1>(preResult) = preCond.second;
          std::get<2>(preResult) = p;
          if (!result) {
            std::get<0>(preResult) = ERROR;
            errorMessages.push_back(Message(p, true));
            // preConditionResults.push_back(PathResult_t(ERROR, p));
          } else {
            // preConditionResults.push_back(PathResult_t(VALID, p));
            std::get<0>(preResult) = result == 2 ? UNKNOWN : VALID;
          }
          preConditionResults.push_back(preResult);
          precond |= result;
        }
      }

      if (precond || !hasPrecond) {
        int res = checkRule(path);
        if (!res) {
          if (errorMessages.size()) {
            result = PRECOND_ERROR;
          } else {
            result = ERROR;
          }
          errorMessages.push_back(Message(path));
          CompletePathResult_t pathResult(PathResult_t(ERROR, path),
                                          preConditionResults);
          pathResults.push_back(pathResult);
        } else {
          CompletePathResult_t pathResult(PathResult_t(res == 2 ? UNKNOWN : VALID, path),
                                          preConditionResults);
          pathResults.push_back(pathResult);
          //                        errs() << "VALID PATH:\n";
          //                        path->dump(true);
          //                        errs() << "------------------------\n";
        }
      } else {
        // TODO: this is only for debug purposes to keep ALL paths
        int res = checkRule(path);
        if (!res) {
          if (errorMessages.size()) {
            result = PRECOND_ERROR;
          } else {
            result = ERROR;
          }
          errorMessages.push_back(Message(path));
          CompletePathResult_t pathResult(PathResult_t(ERROR, path),
                                          preConditionResults);
          pathResults.push_back(pathResult);
        } else {
          CompletePathResult_t pathResult(PathResult_t(res == 2 ? UNKNOWN : VALID, path),
                                          preConditionResults);
          pathResults.push_back(pathResult);
          //                        errs() << "VALID PATH:\n";
          //                        path->dump(true);
          //                        errs() << "------------------------\n";
        }
      }

      //                for (auto &m : errorMessages) {
      //                    m.dump();
      //                    errs() << "\n\n";
      //                }
    }
    //        }
  }
  //    if (preconditions()) {
  //
  //        for (auto &child : children) {
  //            if (child->getType() == RULE) {
  //                ((Rule*)child)->checkRule();
  //            } else {
  //                for (auto &path : paths) {
  //                    if (!checkConstraint(path->getLast())) {
  //                        path->dump();
  //                    }
  //                }
  //            }
  //        }
  //
  //    } else {
  //        return true;
  //    }
  return false;
}

int Rule::checkRule(Path *path) const {
  return checkConstraint(path->getLast());
}

Rule::PathList_t Rule::getPaths(const Instruction *inst) const {
  PathList_t foundPaths;
  for (auto &path : paths) {
    if (path->getEntry()->getNext() &&
        path->getEntry()->getNext()->getElement() == inst) {
      foundPaths.push_back(path);
    }
  }
  return foundPaths;
}

void Rule::addPaths(PathList_t paths) {
  this->paths.insert(this->paths.end(), paths.begin(), paths.end());
}

std::string Rule::getRuleTitle() const { return ruleTitle; }

bool Rule::operator==(const Rule &other) const {
  if (ruleTitle.size()) {
    if (other.ruleTitle.size()) {
      return ruleTitle == other.ruleTitle;
    }
    return false;
  }
  if (relevantLocation && relevantLocation == other.getRelevantLocation())
    return true;
  return false;
}

//------------------------------------------
// CallConstraint
//------------------------------------------

CallConstraint::CallConstraint(ConstraintType constraintType,
                               std::string functionName)
    : Constraint(constraintType), functionName(functionName) {}

// 0 => ERROR; 2 => UNKNOWN; 3 => VALID
int CallConstraint::checkConstraint(PathElementBase *pathElement) const {
  const Instruction *inst =
      dyn_cast<const Instruction>(pathElement->getElement());
  if (inst) {
    SimpleCallGraph::FunctionSet_t calledFunctions =
        ptr::getSimpleCallGraph().getCalled(inst);
    for (auto &calledFunction : calledFunctions) {
      if (calledFunction == functionName) {
        return 3;
      }
    }
  }
  return 0;
}

// When backtrace here, we should just jump them and continue;
// Otherwise the process will stop because it met a function call.
bool CallConstraint::shouldStop(PathElementBase *pathElement) const {
  const Instruction *inst =
      dyn_cast<const Instruction>(pathElement->getElement());
  if (!inst) {
    return false;
  }
  if (inst->getOpcode() == Instruction::Call) {
    SimpleCallGraph::FunctionSet_t calledFunctions =
        ptr::getSimpleCallGraph().getCalled(inst);
    for (auto &calledFunction : calledFunctions) {
      if (calledFunction == "objc_retain" ||
          calledFunction == "objc_autoreleaseReturnValue" ||
          calledFunction == "objc_autorelease" ||
          calledFunction == "objc_release" ||
          calledFunction == "objc_retainAutoreleasedReturnValue" ||
          calledFunction == "objc_retainAutorelease" ||
          calledFunction == "objc_msgSend" || 
          calledFunction == "NSSearchPathForDirectoriesInDomains") {

        return false;
      }
      if (calledFunction == functionName) {
        return true;
      }
    }
  }
  return false;
}

// Just make a html result file.
HTMLReportPrinter::HTMLReportPrinter(raw_ostream &file_out)
    : file_out(file_out) {
  printHeader();
}

// Maybe we can use this function to check if pre and initialCriterion inst are the same.
bool checkIfInOnePath(Path *prev, Path *trace) {
  PathElementBase *currentPrev = prev->getEntry();
  PathElementBase *currentTrace = trace->getEntry();

  return false;
}
void HTMLReportPrinter::addScanExistResult(Rule* target_rule){
  static unsigned ruleCounter = 0;
  ruleCounter++;
  file_out<< "<div id = \"rule :" << ruleCounter << "\">\n";
  file_out << "<h1 data-toggle=\"collapse\" href=\"#rule" << ruleCounter
           << "body\">" << target_rule->getRuleTitle() << "</h1>\n";

  file_out << "<div class=\"collapse in   \" id=\"rule" << ruleCounter
           << "body\">\n";
  file_out << "<h3 >"<< "description: "<< target_rule->getRuleDescription()<<"</h3>\n";
  
  for(auto &tmp_criterion : target_rule->getCriterions()){
    file_out << "<h4> the method "<<tmp_criterion.second.first.getFunctionName()<<" is not exist</h4>";
  }

  file_out<<"</div>";
  file_out<<"</div>";
}


void HTMLReportPrinter::addScanNeedCallResult(Rule* target_rule){
  static unsigned ruleCounter = 0;
  ruleCounter++;
  file_out<< "<div id = \"rule :" << ruleCounter << "\">\n";
  file_out << "<h1 data-toggle=\"collapse\" href=\"#rule" << ruleCounter
           << "body\">" << target_rule->getRuleTitle() << "</h1>\n";
  

  file_out << "<div class=\"collapse in   \" id=\"rule" << ruleCounter
           << "body\">\n";
  file_out << "<h3 >"<< "description: "<< target_rule->getRuleDescription()<<"</h3>\n";
  
  for(auto &tmp_criterion : target_rule->getCriterions()){
    file_out << "<h4> the method "<<tmp_criterion.second.first.getFunctionName()<<" is not called</h4>";
  }

  file_out<<"</div>";
  file_out<<"</div>";
}


void HTMLReportPrinter::addScanResult(Rule* target_rule,std::set<std::pair<std::string,std::string>> call_map){
  static unsigned ruleCounter = 0;
  ruleCounter++;
  file_out<< "<div id = \"rule :" << ruleCounter << "\">\n";
  file_out << "<h1 data-toggle=\"collapse\" href=\"#rule" << ruleCounter
           << "body\">" << target_rule->getRuleTitle() << "</h1>\n";
  

  file_out << "<div class=\"collapse in   \" id=\"rule" << ruleCounter
           << "body\">\n";
  file_out << "<h3 >"<< "description: "<< target_rule->getRuleDescription()<<"</h3>\n";
  file_out << "<h4>"<<" level : "<<target_rule->getRuleLevel()<<"</h4>\n";
  file_out << "<h4>"<<" repair suggestion : "<<target_rule->getRuleRepairSug()<<"</h4>\n";
  for(auto &call_pair : call_map){
    file_out << "<div >";
    file_out << call_pair.first<<" is called at : " << call_pair.second <<"</div>\n"; 
  }

  file_out<<"</div>";
  file_out<<"</div>";
}

void HTMLReportPrinter::addResults(
    Rule *rule, const Rule::CompletePathResultList_t &results) {

  static unsigned ruleCounter = 0;
  static unsigned pathCounter = 0;
  ruleCounter++;
  file_out << "<div id=\"rule" << ruleCounter << "\">\n";
  file_out << "<h1 data-toggle=\"collapse\" href=\"#rule" << ruleCounter
           << "body\">" << rule->getRuleTitle() << "</h1>\n";

  file_out << "<div class=\"collapse in   \" id=\"rule" << ruleCounter
           << "body\">\n";

  /*
  add by -death
  */
   file_out << "<h3 >"<< "description: "<< rule->getRuleDescription()<<"</h3>\n";
  file_out << "<h4>"<<" level : "<<target_rule->getRuleLevel()<<"</h4>\n";
  file_out << "<h4>"<<" repair suggestion : "<<target_rule->getRuleRepairSug()<<"</h4>\n";
  /*
  add by -death end
  */

  typedef std::pair<const Value *, const Value *> ValuePair_t;
  typedef std::set<ValuePair_t> ValuePairSet_t;

  ValuePairSet_t printed;

  for (auto &r : results) {
    if(rule->getReversed()==true){
      if(r.first.first!=Rule::VALID){
        continue;
      }
    }
    else{
      if(r.first.first!=Rule::ERROR){
        continue;
      }
    }
    
    if (PrintSameUseDef) {
      ValuePair_t pair(r.first.second->getEntry()->getElement(),
                       r.first.second->getLast()->getElement());
      if (printed.find(pair) != printed.end())
        continue;
      printed.insert(pair);
    }

    bool preCond = r.second.size() ? false : true;
    for (auto &pre : r.second) {
      if (std::get<0>(pre) == Rule::VALID) {
        preCond = true;
      }
    }

    pathCounter++;
    std::stringstream ruleHeaderClasses;
    if (r.first.first == Rule::VALID) {
      ruleHeaderClasses << "text-success ";
    } else if (r.first.first == Rule::ERROR) {
      ruleHeaderClasses << "text-danger ";
    } else if (r.first.first == Rule::UNKNOWN) {
      ruleHeaderClasses << "text-info ";
    }
    file_out << "<div class=\"tracebody "
             << (!preCond || r.first.first == Rule::VALID ? "dismiss" : "")
             << "\">\n";
    file_out << "<div style=\"opacity:0.3; background-color:#000; "
                "height:10px\"></div>\n";
    file_out << "<h2 data-toggle=\"collapse\" href=\"#pathBody" << pathCounter
             << "\" class=\"" << ruleHeaderClasses.str() << "\">"
             << "PATH"
             << " #" << pathCounter << "</h2>\n";
    file_out << "<div class=\"collapse in\" id=\"pathBody" << pathCounter
             << "\">\n";
    for (auto &pre : r.second) {

      std::stringstream preconditionHeaderClasses;

      if (std::get<0>(pre) == Rule::VALID) {
        preconditionHeaderClasses << "text-success ";
      } else if (std::get<0>(pre) == Rule::ERROR) {
        preconditionHeaderClasses << "text-danger ";
      } else if (std::get<0>(pre) == Rule::UNKNOWN) {
        preconditionHeaderClasses << "text-info ";
      }
      file_out << "<h4 class=\"" << preconditionHeaderClasses.str()
               << "\">Precondition: " << std::get<1>(pre)->getRuleTitle()
               << "</h4>\n";
      printPath(std::get<2>(pre), true);
    }

    file_out << "<h3>Trace</h3>\n";
    printPath(r.first.second, false);
    file_out << "</div>\n";
    file_out << "</div>\n";
  }

  file_out << "</div>\n";
  file_out << "</div>\n";
}

void HTMLReportPrinter::printHeader() {
  file_out
      << "<!DOCTYPE html>\n"
         "<html>\n"
         "    <head>\n"
         "        <meta charset=\"utf-8\">\n"
         "        <title></title>\n"
         //                        "<link rel=\"stylesheet\"
         //                        href=\"http://maxcdn.bootstrapcdn.com/bootstrap/3.3.6/css/bootstrap.min.css\">\n"
         //                        "<script
         //                        src=\"https://ajax.googleapis.com/ajax/libs/jquery/1.12.0/jquery.min.js\"></script>\n"
         //                        "<script
         //                        src=\"http://maxcdn.bootstrapcdn.com/bootstrap/3.3.6/js/bootstrap.min.js\"></script>\n"
         "<link rel=\"stylesheet\" href=\"scripts/bootstrap.min.css\">\n"
         "<link rel=\"stylesheet\" href=\"scripts/report.css\">\n"
         "<script src=\"scripts/jquery.min.js\"></script>\n"
         "<script src=\"scripts/bootstrap.min.js\"></script>\n"
         "<script src=\"scripts/helper.js\"></script>\n"
         "    </head>\n"
         "    <body>\n";
}

void HTMLReportPrinter::printFooter() {
  file_out << "    </body>\n"
              "</html>\n";
}

void HTMLReportPrinter::close() {
  printFooter();
  file_out.flush();
}

void HTMLReportPrinter::printPath(Path *path, bool collapsable) {
  static unsigned pathID = 0;
  bool inOne = false;
  std::stringstream ss;
  ss << "path" << pathID++;
  PathElementBase *current = path->getEntry();

  if (collapsable) {
    file_out << "<a data-toggle=\"collapse\" href=\"#" << ss.str()
             << "\">Show/Hide</a>\n";
  }

  std::stringstream classes;
  classes << "collapse ";
  if (!collapsable) {
    classes << " in";
  }

  file_out << "<div id=\"" << ss.str() << "\" class=\"" << classes.str()
           << "\">\n";
  while (current) {
    file_out << "<div class=\"path-element\" data-instid=\""
             << utohexstr((uint64_t)current->getElement()) << "\">";
    //        current->print(file_out);
    if (const Instruction *inst =
            dyn_cast<const Instruction>(current->getElement())) {
      file_out << inst->getParent()->getParent()->getName();
    }
    file_out << current->getElement() << " ";
    current->getElement()->print(file_out);
    file_out << "(" << *current->getRelevantVariable() << ")";
    if (const CallInst *callInst =
            dyn_cast<const CallInst>(current->getElement())) {
      const SimpleCallGraph::FunctionSet_t &calledFunctions =
          ptr::getSimpleCallGraph().getCalled(callInst);
      if (calledFunctions.size()) {
        file_out << "<div class=\"border-left-small\">\n"
                    "<div class=\"call-label\">Called:</div>\n";
        for (auto &calledFunction : calledFunctions) {
          file_out << "<div class=\"call-entry\">" << calledFunction
                   << "</div>\n";
        }
        file_out << "</div>\n";
      }
    } else if (dyn_cast<const ConstantInt>(current->getElement())) {

      if (current->getType() == PathElementBase::ConstAddressElement) {
        file_out << "<div>" << ((ConstPathElement *)current)->getValue()
                 << "</div>\n";
      }
    }
    file_out << "</div>\n";
    current = current->getNext();
  }
  file_out << "</div>\n";
}
