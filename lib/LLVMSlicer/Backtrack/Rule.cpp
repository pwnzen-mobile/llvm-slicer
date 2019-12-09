#include <llvm/Support/raw_ostream.h>
#include "Rule.h"
#include "json.hpp"
#include "Constraint.h"

#include <vector>
#include <map>
#include <llvm/Support/CommandLine.h>
#include <fstream>

using namespace llvm;
using namespace llvm::slicing;

using json = nlohmann::json;
using std::string;
using std::map;
using std::vector;

cl::opt<std::string> RulesFile("rules", cl::desc("r"), cl::init(""), cl::Hidden);

/*
\todo{crazy! bad grammar! re-design later}
*/

uint64_t translateRegister(string reg) {
    if (reg == "X0")
        return 5;
    if (reg == "X1")
        return 6;
    if (reg == "X2")
        return 7;
    if (reg == "X3")
        return 8;
    if (reg == "X4")
        return 9;
    if (reg == "X5")
        return 10;
    if (reg == "X6")
        return 11;
    if (reg == "X7")
        return 12;
    if (reg == "X8")
        return 13;
    return -1U;

}

typedef map<string, vector<Parameter>> CallMap_t;
CallMap_t callMap;

void dumpJSON(json &j) {
    errs() << j.dump();
}

Constraint *parseCondition(json &cond);

/*
 name:          name of the criterion. a) backbone of the criterion is used for title of the report. b) key of the criterion.
 criterion:     pointer (point to name) for the criterion.
 conditions:    checker for the criterion.
 */

Rule *parseRule(json &rule, bool precondition) {

    if (rule.find("name") == rule.end() ||
        rule.find("conditions") == rule.end() ||
        rule.find("criterion") == rule.end()) {
        return nullptr;
    }

    if (!rule["conditions"].is_array()) {
        llvm_unreachable("malformed");
    }

    Rule *r = new Rule(rule["name"].get<string>(), Constraint::STRICT, ChainConstraint::OR);
    vector<Rule*> preConditions;

     /*
    add by -death
     */
    if(rule.find("description")==rule.end()){
        errs()<<"rule no description\n";
        //return nullptr;
    }
    else{
        if(rule["description"].is_string()==false){
            errs()<<"rule description not true\n";
            return nullptr;
        }
        r->setRuleDescription(rule["description"].get<string>());
    }
    if(rule.find("spcialtype")==rule.end()){
        r->setReversed = false;
    }
    else{
        if(rule["specialtype"].is_string() == false){
            errs()<<" rule level is not a string\n";
            return nullptr;
        }
        if(rule["specialtype"].get<string>()=="true"){
            r->setReversed = true;
        }
        else{
            r->setReversed = false;
        }
    }
    if(rule.find("level")==rule.end()){
        errs()<<"rule no level\n";
    }
    else{
        if(rule["level"].is_string() == false){
            errs()<<" rule level is not a string\n";
            return nullptr;
        }
        r->setRuleLevel(rule["level"].get<string>());
    }
    if(rule.find("repair_suggest")==rule.end()){
        errs()<<"rule no level\n";
    }
    else{
        if(rule["repair_suggest"].is_string() == false){
            errs()<<" rule level is not a string\n";
            return nullptr;
        }
        r->setRuleLevel(rule["repair_suggest"].get<string>());
    }
    /*
    add by -death end 
     */

    for (auto &cond : rule["conditions"]) {
        string type = cond["type"];
        if (type != "PRE")
            continue;

        Rule *p = parseRule(cond, true);

        preConditions.push_back(p);
    }
    for (auto &cond : rule["conditions"]) {
        string type = cond["type"];
        if (type == "PRE") {
            continue;
        }
        r->addConstraint(parseCondition(cond));
    }

    if (rule["criterion"].is_string()) {
        if (callMap.find(rule["criterion"].get<string>()) == callMap.end()) {
            errs() << rule["criterion"].dump() << "\n";
            llvm_unreachable("");
        }
        for (auto &p : callMap[rule["criterion"]]) {
            r->addCriterion(p, preConditions);
        }
    } else if (rule["criterion"].is_array()) {
        for (auto &param : rule["criterion"]) {
            Parameter::ParameterType type = Parameter::PRE;
            if (param.find("type") != param.end()) {
                llvm_unreachable("TODO");
            }
            r->addCriterion(
                    Parameter(param["name"].get<string>(), translateRegister(param["parameter"].get<string>()), type),
                    preConditions);
        }
    } else {
        llvm_unreachable("");
    }
    if (rule.find("parent") != rule.end()) {
        r->setParentRuleTitle(rule["parent"].get<string>());
    }
    return r;
}

// TODO: Add other types here.
Constraint *parseCondition(json &cond) {
    Constraint::ConstraintType type = Constraint::STRICT;
    if (cond["type"] == "PRE") {
        type = Constraint::PRECONDITION;
    }
    if (cond.find("calls") != cond.end()) {
        ChainConstraint *orConstraint = new ChainConstraint(Constraint::STRICT, ChainConstraint::OR);

        if (callMap.find(cond["calls"].get<string>()) == callMap.end()) {
            errs() << cond["calls"].dump() << "\n";
            llvm_unreachable("");
        }
        for (auto &p : callMap[cond["calls"].get<string>()]) {
            CallConstraint *constr = new CallConstraint(Constraint::STRICT, p.getFunctionName());
            orConstraint->addConstraint(constr);
        }
        return orConstraint;
    } else if (cond["conditionType"].get<string>() == "ConstInt") {
        if (cond.find("equal") != cond.end()) {
            return new llvm::slicing::ConstConstraint(ConstConstraint::EQUAL, type, cond["equal"].get<int>(), "", std::vector<std::string>());
        } else if (cond.find("greater") != cond.end()) {
            return new llvm::slicing::ConstConstraint(ConstConstraint::GREATER, type, cond["greater"].get<int>(), "", std::vector<std::string>());
        } else if (cond.find("loreq") != cond.end()) {
            return new llvm::slicing::ConstConstraint(ConstConstraint::LOREQ, type, cond["loreq"].get<int>(), "", std::vector<std::string>());
        }else if (cond.find("lorneq") != cond.end()) {
            return new llvm::slicing::ConstConstraint(ConstConstraint::LORNEQ, type, cond["lorneq"].get<int>(), "", std::vector<std::string>());
        } else {
            return new llvm::slicing::ConstConstraint(ConstConstraint::ANY, type, 0, "", std::vector<std::string>());
        }
    } else if (cond["conditionType"].get<string>() == "ConstStr" || cond["conditionType"].get<string>() == "ConstType") {
        // condition string can be a const string or string list, we insert strings into a vector.
        // If in, then cond["in"] is equal or just included in the string list.
        if (cond.find("in") != cond.end()) {
            std::vector<std::string> vs;
            if(cond["in"].is_array()) {
                for (string s : cond["in"]) {
                    vs.push_back(s);
                }
            } else {
                vs.push_back(cond["in"]);
            }
            errs() << "[+]vs.size: " << vs.size() << "\n";
            return new llvm::slicing::ConstConstraint(ConstConstraint::IN, type, 0, "", vs);
        } else if (cond.find("notin") != cond.end()) {
            std::vector<std::string> vs;
            if(cond["notin"].is_array()) {
                for (string s : cond["notin"]) {
                    vs.push_back(s);
                }
            } else {
                vs.push_back(cond["notin"]);
            }
            return new llvm::slicing::ConstConstraint(ConstConstraint::NOTIN, type, 0, "", vs);
        } else {
            return new llvm::slicing::ConstConstraint(ConstConstraint::ANY, type, 0, "", std::vector<std::string>());
        }
/*
 rules for:
 NSDictionary * options = @{
 GCDWebServerOption_Port: @(8080),
 GCDWebServerOption_BindToLocalhost: @(YES),
 GCDWebServerOption_ServerName: @"Ionic"
 };
 [webServer startWithOptions:options error:nil];
 
 I do not like this grammar, it's somewhat unreasonable and mysticism.
 TODO: X2:[GCDWebServerOption_BindToLocalhost] -> X2_GCDWebServerOption_BindToLocalhost
 Refer to: Nenad Jovanovic's phd thesis `web application security'
 */
    } else if (cond["conditionType"].get<string>() == "ConstDict") {
        // Directory type
        std::map<string, string> strDict;
        std::map<string, int> intDict;
        std::set<map<string, string>> strDicts;
        std::set<map<string, int>> intDicts;

        if (cond["exits"].is_array()) {
            for (auto &d : cond["in"]) {
                if (d["valueType"].get<string>() == "int") {
                    intDict.insert(std::pair<string, int>(d["key"], d["value"].get<int>()));
                    intDicts.insert(intDict);
                } else if (d["valueType"].get<string>() == "string") {
                    strDict.insert(std::pair<string, string>(d["key"], d["value"].get<string>()));
                    strDicts.insert(strDict);
                }
            }
        } else {
            if (cond["exits"]["valueType"].get<string>() == "int") {
                intDict.insert(std::pair<string, int>(cond["in"]["key"], cond["in"]["value"].get<int>()));
                intDicts.insert(intDict);
            } else if (cond["exits"]["valueType"].get<string>() == "string") {
                strDict.insert(std::pair<string, string>(cond["exits"]["key"], cond["in"]["value"].get<string>()));
                strDicts.insert(strDict);
            }
        }
        return new llvm::slicing::ConstConstraint(ConstConstraint::EXITS, type, 0, intDicts, strDicts);
    } else if (cond["conditionType"].get<string>() == "NOT") {
        ChainConstraint *notChain = new llvm::slicing::ChainConstraint(Constraint::STRICT, ChainConstraint::NOT_AND);
        for (auto &subCond : cond["conditions"]) {
            notChain->addConstraint(parseCondition(subCond));
        }
        return notChain;
    } else {
        llvm_unreachable("");
    }
    return nullptr;
}

std::vector<Rule*> llvm::slicing::parseRules() {
    if (RulesFile.size() == 0) {
        errs() << "No rule specified\n";
        llvm_unreachable("No rules specified");
    }
    std::ifstream inFile;
    inFile.open(RulesFile);//open the input file

    if (!inFile.is_open()) {
        errs() << "Cant find rule file\n";
        llvm_unreachable("");
    }

//    std::string content((std::istreambuf_iterator<char>(inFile)), std::istreambuf_iterator<char>());

    json j = json::parse(inFile);
    std::vector<Rule*> rules;

    if (!j.is_array()) {    // rule file should start with `[' and ends with `]'
//        errs() << content;
        llvm_unreachable("malformed rules");
    }
    
    // parse `calls' section
    for (size_t i = 0; i < j.size(); ++i) {
        if (j[i].find("calls") != j[i].end()) {
            if (!j[i]["calls"].is_array()) {
                llvm_unreachable("malformed rules");
            }

            string callsName = j[i]["name"];

            for (auto &c : j[i]["calls"]) {
                if (c.find("name") == c.end() || c.find("parameter") == c.end()) {
                    errs() << c.dump() << "\n";
                    llvm_unreachable("malformed rules");
                }
                string name = c["name"].get<string>();
                string parameter = c["parameter"];

                Parameter::ParameterType type = Parameter::PRE;
                if (c.find("type") != c.end()) {
                    llvm_unreachable("TODO");
                }

                uint64_t regNo = translateRegister(parameter);  /* registers supported are ranging from X0-X8 */

                llvm::slicing::Parameter p(name, regNo, type);

                callMap[callsName].push_back(p);
            }
        }
    }

    // support multi rules in one file?
    for (auto &rule: j) {
        Rule *r = parseRule(rule, false);
        if (r) {
            rules.push_back(r);
        }
//        if (rule.find("name") == rule.end() ||
//                rule.find("conditions") == rule.end() ||
//                rule.find("criterion") == rule.end()) {
//            continue;
//        }
//
//        if (!rule["conditions"].is_array()) {
//            llvm_unreachable("malformed");
//        }
//
//        vector<Rule*> preConditions;
//
//
//
//        for (auto &cond : rule["conditions"]) {
//            string type = cond["type"];
//            if (type != "PRE")
//                continue;
//            Rule *r = new Rule("", Constraint::PRECONDITION, ChainConstraint::AND);
//
//            if (cond["conditionType"].get<string>() == "ConstInt") {
//                if (cond.find("equal") != cond.end()) {
//                    r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::EQUAL, cond["equal"].get<int>(), Constraint::PRECONDITION));
//                } else if (cond.find("greater") != cond.end()) {
//                    r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::GREATER, cond["greater"].get<int>(), Constraint::PRECONDITION));
//                } else {
//                    errs() << cond.dump() << "\n";
//                    llvm_unreachable("");
//                }
//            } else {
//                llvm_unreachable("");
//            }
//
//            if (cond["calls"].is_string()) {
//                if (callMap.find(cond["calls"].get<string>()) == callMap.end()) {
//                    errs() << cond["calls"].get<string>() << "\n";
//                    llvm_unreachable("malformed");
//                }
//
//                for (auto &p : callMap[cond["calls"].get<string>()]) {
//                    r->addCriterion(p, {});
//                }
//
//            }
//
//            preConditions.push_back(r);
//        }
//
//        Rule *r = new Rule(rule["name"].get<string>(), Constraint::STRICT, ChainConstraint::OR);
//
//        if (rule["criterion"].is_string()) {
//            if (callMap.find(rule["criterion"].get<string>()) == callMap.end()) {
//                errs() << rule["criterion"].dump() << "\n";
//                llvm_unreachable("");
//            }
//            for (auto &p : callMap[rule["criterion"]]) {
//                r->addCriterion(p, preConditions);
//            }
//        } else if (rule["criterion"].is_array()) {
//            for (auto &param : rule["criterion"]) {
//                Parameter::ParameterType type = Parameter::PRE;
//                if (param.find("type") != param.end()) {
//                    llvm_unreachable("TODO");
//                }
//                r->addCriterion(Parameter(param["name"].get<string>(), translateRegister(param["parameter"].get<string>()), type), preConditions);
//            }
//        } else {
//            llvm_unreachable("");
//        }
//
//        for (auto &cond : rule["conditions"]) {
//            string type = cond["type"];
//            if (type == "PRE") {
//                continue;
//            }
//
//            if (cond.find("calls") != cond.end()) {
//                ChainConstraint *orConstraint = new ChainConstraint(Constraint::STRICT, ChainConstraint::OR);
//
//                if (callMap.find(cond["calls"].get<string>()) == callMap.end()) {
//                    errs() << cond["calls"].dump() << "\n";
//                    llvm_unreachable("");
//                }
//                for (auto &p : callMap[cond["calls"].get<string>()]) {
//                    CallConstraint *constr = new CallConstraint(Constraint::STRICT, p.getFunctionName());
//                    orConstraint->addConstraint(constr);
//                }
//
//                r->addConstraint(orConstraint);
//            } else if (cond.find("conditionType") != cond.end()) {
//                if (cond["conditionType"] == "ConstInt") {
//                    if (cond.find("equal") != cond.end()) {
//                        r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::EQUAL, cond["equal"].get<int>(), Constraint::STRICT));
//                    } else if (cond.find("greater") != cond.end()) {
//                        r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::GREATER, cond["greater"].get<int>(), Constraint::STRICT));
//                    } else if (cond.find("loreq") != cond.end()) {
//                        r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::LOREQ, cond["loreq"].get<int>(), Constraint::STRICT));
//                    }else if (cond.find("lorneq") != cond.end()) {
//                        r->addConstraint(new llvm::slicing::ConstConstraint(ConstConstraint::LORNEQ, cond["lorneq"].get<int>(), Constraint::STRICT));
//                    } else {
//                        errs() << cond.dump() << "\n";
//                        llvm_unreachable("");
//                    }
//                }
//            }
//        }
//
//        rules.push_back(r);
    }
    return rules;
}
