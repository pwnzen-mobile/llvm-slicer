#include <map>
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/Andersen/IntraDFAInit.h"
#include "llvm/IR/LegacyPassManager.h"

#include "BuildCallGraph.h"
#include "RuleExpressions.h"

#include "../Languages/LLVM.h"

namespace llvm {
namespace ptr {
namespace detail {

class CallMaps {
	private:

};
}}}
