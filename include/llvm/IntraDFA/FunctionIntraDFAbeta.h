#include "llvm/Pass.h"

namespace llvm {
namespace beta {}

class FunctionIntraDFAbeta : public ModulePass {
public:
  static char ID;

  FunctionIntraDFAbeta() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M);

  void getAnalysisUsage(AnalysisUsage &AU) const;
};
} // namespace llvm
