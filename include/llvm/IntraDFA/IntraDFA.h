#ifndef LLVM_INTRADFA_H_H
#define LLVM_INTRADFA_H_H

#include "llvm/Pass.h"

namespace llvm {
class FunctionSlicer : public ModulePass {
public:
  static char ID;

  FunctionSlicer() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M);

  void getAnalysisUsage(AnalysisUsage &AU) const;
};
} // namespace llvm

#endif