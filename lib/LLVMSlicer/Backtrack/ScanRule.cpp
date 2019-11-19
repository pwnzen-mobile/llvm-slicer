#include <llvm/Support/raw_ostream.h>
#include "ScanRule.h"
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

cl::opt<std::string> ScanRulesFile("scan_rules", cl::desc("r"), cl::init(""), cl::Hidden);



uint64_t getX0Reg() {
    return 5;/* X0 */

}



void llvm::slicing::parseScanRules(std::vector<Rule*>* c_rule_vec, std::vector<Rule*>* objc_rule_vec) {
    if (ScanRulesFile.size() == 0) {
        errs() << "No scan rule specified\n";
        llvm_unreachable("No scan rules specified");
    }
    std::ifstream inFile;
    inFile.open(ScanRulesFile);//open the input file

    if (!inFile.is_open()) {
        errs() << "Cant find scan rule file\n";
        llvm_unreachable("");
    }

//    std::string content((std::istreambuf_iterator<char>(inFile)), std::istreambuf_iterator<char>());

    json j = json::parse(inFile);

    if (!j.is_array()) {    
        llvm_unreachable("malformed rules");
    }
    for (auto &scanrule: j) {
        if(scanrule.find("name")==scanrule.end() || 
            scanrule.find("description")==scanrule.end() || 
            scanrule.find("method_type")==scanrule.end() || 
            scanrule.find("method_name")==scanrule.end()){
                errs()<<"rule file is not correct\n";
                llvm_unreachable("malformed");
            }
        if(!scanrule["method_type"].is_string()){
            errs()<<"method_type is not a string\n";
            llvm_unreachable("malformed");
        }
        if(!scanrule["name"].is_string()){
            errs()<<"name is not a string\n";
            llvm_unreachable("malformed");
        }
        if(!scanrule["description"].is_string()){
            errs()<<"description is not a string\n";
            llvm_unreachable("malformed");
        }
        
        
            Rule *tmp_r = new Rule(scanrule["name"].get<std::string>(), Constraint::STRICT, ChainConstraint::OR);
            std::vector<Rule*> tmp_pre;
            if(scanrule["method_name"].is_string()){
                Parameter::ParameterType type = Parameter::PRE;
                tmp_r->addCriterion(
                    Parameter(scanrule["method_name"].get<string>(),getX0Reg(),type),
                    tmp_pre
                );
            }else if(scanrule["method_name"].is_array()){
                for(auto &param : scanrule["method_name"]){
                    Parameter::ParameterType type = Parameter::PRE;
                    tmp_r->addCriterion(
                        Parameter(param.get<string>(),getX0Reg(),type),
                        tmp_pre
                    );
                }
            }else{
                errs()<<"method name is not correct\n";
                llvm_unreachable("malformed");
            }
        if(scanrule["method_type"].get<string>()=="C"){
            c_rule_vec->push_back(tmp_r);
        }
        else{
            objc_rule_vec->push_back(tmp_r);
        }
        
    }
}
