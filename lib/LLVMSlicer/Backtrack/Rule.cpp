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
use the new grammer for the rule : 
   {
       "name" : "",
        "level"  : "",
        "description" : "",
        "repair_suggestion" : "",
        "criterion" : [{
                "name": "",
                "register" : ""
        }
        ],
        "PreCon" : [
                 "criterion" : [{
                                "name" : "",
                                "register" : ""
                 }],
                 "PreConditionType" : "",
                 "condition" : [
                     {
                         "valueType" : "",
                         "relationType" : "",
                         "value" : 
                     }
                 ]
        ],
        "condition" : [
            {
                "valueType" : "",
                "relationType" : "",
                "value" : 
            }
        ]
   }

    PreCon : "PreConditionType" = "call", "not call", "call with condition"

    condition : "valueType" :"ConstInt" , "relationType" : "eq" , "ne","low", "nlow" , "greater", "ngreater" , "in ", "notin"
                                                        "constStr", "relationType" : "eq", "ne", "startwith", "nstartwith", "endwith", "nendwith", "in", "notin"
                                                        "Dict" ,  "relationType" : "in" , "notin" ,  "value" : {"key" : ,  "value"}  , "relationType" : "haskey", "nhaskey",  "value" : 
                            

*/

std::vector<Rule*> llvm::slicing::parseRules() {
    
}