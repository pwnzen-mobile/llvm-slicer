#ifndef LLVM_CONSTRAINT_H
#define LLVM_CONSTRAINT_H

#include "Path.h"
#include <set>
#include <string>
#include <vector>

namespace llvm {
namespace slicing {

class Rule;

class Parameter {
public:
  enum ParameterType { PRE, POST };
  Parameter(std::string functionName, uint64_t regNo,
            ParameterType parameterType);

  std::string getFunctionName() const;
  uint64_t getRegNo() const;
  ParameterType getParameterType() const;

private:
  std::string functionName;
  uint64_t regNo;
  ParameterType parameterType;
};

class Message {
public:
  Message(Path *path, bool isPrecondition = false);

  void dump();

private:
  bool isPrecondition;
  Path *path;
};

typedef struct {
  std::vector<const ConstantInt *> keys;
  std::vector<const ConstantInt *> values;
  int num;
} Dictionary;

class Constraint {
public:
  typedef std::vector<const Constraint *> ConstraintList_t;
  enum ConstraintType { STRICT, WARN, PRECONDITION, UNSPECIFIED };

  enum Type { CONSTRAINT, RULE };

  Constraint(ConstraintType constraintType);

  virtual ~Constraint(){};

  virtual void addConstraint(const Constraint *constraint);

  virtual int checkConstraint(PathElementBase *pathElement) const = 0;
  virtual bool shouldStop(PathElementBase *pathElement) const = 0;

  virtual Type getType() const;
  ConstraintType getConstraintType() const;

  const ConstraintList_t &getChildren() const;

protected:
  ConstraintList_t children;
  ConstraintType constraintType;

private:
};

class ChainConstraint : public Constraint {
public:
  enum ChainType { AND, OR, NOT_AND };

  ChainConstraint(ConstraintType constraintType, ChainType chainType);

  virtual int checkConstraint(PathElementBase *pathElement) const;
  virtual bool shouldStop(PathElementBase *pathElement) const;

protected:
  ChainType chainType;
};

class Rule : public ChainConstraint {
public:
  typedef std::vector<const Instruction *> InstructionList_t;

  typedef std::pair<Parameter, std::vector<Rule *>> Criterion_t;
  typedef std::vector<Criterion_t> ParameterList_t;
  typedef std::pair<const Rule *, Parameter> RuleParameter_t;
  typedef std::vector<RuleParameter_t> RuleParameterList_t;
  typedef std::pair<const Rule *, Criterion_t> RuleCriterion_t;
  typedef std::vector<RuleCriterion_t> RuleCriterionList_t;
  typedef std::vector<Path *> PathList_t;
  typedef std::pair<const Instruction *, Rule *> InstructionRule_t;
  typedef std::vector<InstructionRule_t> InstructionRuleList_t;
  typedef std::pair<std::pair<const Instruction *, const Instruction *>,
                    InstructionRuleList_t>
      InitialInstructionPair_t;
  typedef std::vector<InitialInstructionPair_t> InitialInstructionList_t;

  typedef std::vector<Message> MessageList_t;

  enum Result { ERROR, PRECOND_ERROR, UNKNOWN, VALID };

  typedef std::pair<Result, Path *> PathResult_t;
  typedef std::tuple<Result, Rule *, Path *> PrecondResult_t;
  typedef std::vector<PathResult_t> PathResultList_t;
  typedef std::vector<PrecondResult_t> PrecondResultList_t;
  typedef std::pair<PathResult_t, PrecondResultList_t> CompletePathResult_t;
  typedef std::vector<CompletePathResult_t> CompletePathResultList_t;

  Rule(std::string ruleTitle, ConstraintType constraintType,
       ChainType chainType);
  Rule(const Rule &base, const llvm::Value *criterion);

  void addInitialInstruction(const Instruction *callInst,
                             const Instruction *paramInst,
                             InstructionRuleList_t preconditionInstruction);
  const InitialInstructionList_t &getInitialInstruction() const;

  virtual int checkConstraint(PathElementBase *pathElement) const;
  virtual bool shouldStop(PathElementBase *pathElement) const;
  virtual bool dismissPath(PathElementBase *pathElementBase) const;

  void addCriterion(Parameter parameter, std::vector<Rule *> preconditions);
  RuleCriterionList_t getCriterions() const;

  virtual Type getType() const;

  virtual void addConstraint(const Constraint *constraint);

  bool preconditions() const;
  bool checkRule();
  int checkRule(Path *path) const;

  void addPaths(PathList_t paths);
  std::string getRuleTitle() const;

  const CompletePathResultList_t &getResults() const { return pathResults; };

  const PathList_t &getPaths() const { return paths; }

  std::vector<const llvm::Value *> getRelevantVariables() const {
    return relevantVariables;
  }

  const llvm::Value *getRelevantLocation() const { return relevantLocation; }

  bool operator==(const Rule &other) const;

  void setParentRuleTitle(std::string parent) { parentRuleTitle = parent; }

  std::string getParentRuleTitle() const { return parentRuleTitle; }

  void setParentRule(Rule *r) { parentRule = r; }

  bool useParentPath(Path *path);

  void setDismissable(Path *path) { dismissablePaths.insert(path); }

  void removeDismissablePaths() {
    for (auto &d : dismissablePaths) {
      while (std::find(paths.begin(), paths.end(), d) != paths.end()) {
        paths.erase(std::find(paths.begin(), paths.end(), d));
      }
    }
  }
  /*
  add by -death 
   */
  void setRuleDescription(std::string des){
    ruleDescription = des;
  }
  void setRuleLevel(std::string level){
    ruleLevel = level;
  }
  void setRuleRepairSug(std::string repair_sug){
    ruleRepairSug = repair_sug;
  }
  void setIsCMethod(bool C){
    is_C_method = C;
  }
  std::string getRuleDescription(){
    return ruleDescription;
  }
  std::string getRuleLevel(){
    return ruleLevel;
  }
  std::string getRuleRepairSug(){
    return ruleRepairSug;
  }
  bool needCall(){
    return need_call;
  }
  void setNeedCall(bool need){
    need_call = need;
  }
  void setReversed(bool reversed){
    RuleReversed = reversed;
  }
  void getReversed(){
    return RuleReversed;
  }
  /*
  add by -death end 
   */

private:
  std::string ruleTitle;
  /*
  add by -death
   */
  std::string ruleDescription;
  std::string ruleLevel;
  std::string ruleRepairSug;
  bool is_C_method;
  bool need_call;
  bool RuleReversed;

  /*
  add by -death end 
   */
  InitialInstructionList_t initialInstructions;
  ParameterList_t criterions;
  PathList_t paths;

  PathList_t getPaths(const Instruction *inst) const;

  bool checkedPaths = false;
  CompletePathResultList_t pathResults;

  std::vector<const llvm::Value *> relevantVariables;
  const llvm::Value *relevantLocation;
  std::string parentRuleTitle;
  Rule *parentRule;
  std::set<Path *> dismissablePaths;
};


class ConstConstraint : public Constraint {
public:
  enum Compare { EQUAL, GREATER, LOREQ, LORNEQ, IN, NOTIN, EXITS, ANY };
  ConstConstraint(Compare compare, ConstraintType constraintType,
                  uint64_t value, std::string strvalue,
                  std::vector<std::string> strings);
  ConstConstraint(Compare compare, ConstraintType constraintType,
                  uint64_t value,
                  std::set<std::map<std::string, int>> intDicts, std::set<std::map<std::string, std::string>> strDicts);
  // ConstConstraint(Compare compare, std::string strvalue, ConstraintType
  // constraintType); ConstConstraint(Compare compare, std::vector<std::string>
  // strings, ConstraintType constraintType);

  virtual int checkConstraint(PathElementBase *pathElement) const;
  virtual bool shouldStop(PathElementBase *pathElement) const;

private:
  uint64_t value;
  std::string strvalue;
  std::vector<std::string> strings;
  std::set<std::map<std::string, int>> intDicts;
  std::set<std::map<std::string, std::string>> strDicts;
  Compare compare;
};

class CallConstraint : public Constraint {
public:
  CallConstraint(ConstraintType constraintType, std::string functionName);

  virtual int checkConstraint(PathElementBase *pathElement) const;
  virtual bool shouldStop(PathElementBase *pathElement) const;

private:
  std::string functionName;
};

class HTMLReportPrinter {
public:
  HTMLReportPrinter(raw_ostream &file_out);
  void addResults(Rule *rule, const Rule::CompletePathResultList_t &results);
  void addScanResult(Rule *rule, std::set<std::pair<std::string,std::string>>);
  void addScanExistResult(Rule*);
  void addScanNeedCallResult(Rule*);
  void close();

private:
  raw_ostream &file_out;
  void printHeader();
  void printFooter();
  void printPath(Path *path, bool collapsable);
};
} // namespace slicing
} // namespace llvm

#endif // LLVM_CONSTRAINT_H
