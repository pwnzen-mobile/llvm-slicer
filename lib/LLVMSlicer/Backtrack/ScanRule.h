#ifndef LLVM_SCANRULE_H
#define LLVM_SCANRULE_H

#include <string>
#include <set>
#include <assert.h>
#include "Rule.h"

#include "Path.h"

namespace llvm {

    class Instruction;

    namespace slicing {

        class ScanRule;

        void parseScanRules(std::vector<llvm::slicing::Rule*>*,std::vector<llvm::slicing::Rule*>*,std::set<llvm::slicing::Rule*>*,std::set<llvm::slicing::Rule*>*);
    }
}

#endif //LLVM_RULE_H
