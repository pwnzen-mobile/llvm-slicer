#ifndef LLVM_RULE_H
#define LLVM_RULE_H

#include <string>
#include <set>
#include <assert.h>

#include "Path.h"

namespace llvm {

    class Instruction;

    namespace slicing {

        class ScanRule;

        std::vector<Rule*> parseScanRules();
    }
}

#endif //LLVM_RULE_H
