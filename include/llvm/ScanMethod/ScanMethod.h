#ifndef LLVM_SCANMETHOD_H_H
#define LLVM_SCANMETHOD_H_H

#include "llvm/Pass.h"

namespace llvm {

    

    class ScanMethod : public ModulePass {
    public:
        static char ID;

        ScanMethod() : ModulePass(ID) {}

        virtual bool runOnModule(Module &M);

        //void getAnalysisUsage(AnalysisUsage &AU) const;
    };
}


#endif //LLVM_SCANMETHOD_H_H
