//===--- llvm-slicer.cpp - The low-level LLVM assembler -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/LLVMSlicer/StaticSlicer.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include <llvm/IR/NoFolder.h>
#include "llvm/IR/Verifier.h"
#include "llvm/Analysis/PostDominators.h"
#include "../../lib/LLVMSlicer/Slicing/PostDominanceFrontier.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Pass.h"
#include <memory>
#include <llvm/Analysis/Andersen/StackAccessPass.h>
#include <llvm/Analysis/Andersen/DetectParametersPass.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>

using namespace llvm;

// https://llvm.org/docs/CommandLine.html#positional-options
static cl::opt<bool>
EnableIntra("enable-intra",
            cl::desc("Enable intra-procedure analysis"));

// errs() << EnableIntra << '\n';
// value is initialized with the defaut constructor, that is 0
// use argument -enable-intra, -enable-intra=true or -enable-intra=false

/*
./llvm-slicer -help
OVERVIEW: llvm .ll -> .bc assembler

USAGE: llvm-slicer [options] <input .llvm file>

OPTIONS:

General options:

-enable-hcd            - Enable the hybrid cycle detection algorithm
-enable-hu             - Enable the HU constraint optimization
-enable-hvn            - Enable the HVN constraint optimization
-enable-intra          - Enable intra-procedure analysis
-enable-lcd            - Enable the lazy cycle detection algorithm
-enable-objc-arc-opts  - enable/disable all ARC Optimizations
-enable-scoped-noalias -
-enable-tbaa           -
-o=<filename>          - Override output filename
-print-after-all       - Print IR after each pass
-print-before-all      - Print IR before each pass
-r=<report>            - Path to HTML report output file
-rng-seed=<seed>       - Seed for the random number generator
-stats                 - Enable statistics output from program (available with Asserts)
-time-passes           - Time each pass, printing elapsed time for each on exit
-verify-dom-info       - Verify dominator info (time consuming)
-verify-loop-info      - Verify loop info (time consuming)
-verify-scev           - Verify ScalarEvolution's backedge taken counts (slow)

Generic Options:

-help                  - Display available options (-help-hidden for more)
-help-list             - Display list of available options (-help-list-hidden for more)
-version               - Display the version of this program

*/

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input .llvm file>"), cl::init("-"));

static cl::opt<std::string>
        OutputFilename("o", cl::desc("Override output filename"),
                       cl::value_desc("filename"));

int main(int argc, char **argv) {
    // Print a stack trace if we signal out.
    sys::PrintStackTraceOnErrorSignal();
    PrettyStackTraceProgram X(argc, argv);

    // https://llvm.org/docs/ProgrammersManual.html#ending-execution-with-llvm-shutdown
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    // https://llvm.org/docs/CommandLine.html#the-cl-parsecommandlineoptions-function
    cl::ParseCommandLineOptions(argc, argv, "llvm .ll -> .bc assembler\n");
    SMDiagnostic Err;
    // https://llvm.org/docs/BitCodeFormat.html
    std::unique_ptr<Module> Mod = parseIRFile(InputFilename, Err, getGlobalContext());
    if (!Mod) {
        Err.print(argv[0], errs());
        return 1;
    }
    // https://llvm.org/docs/WritingAnLLVMPass.html#what-passmanager-does
    legacy::PassManager *PM = new legacy::PassManager();
  
    // https://llvm.org/docs/Passes.html
    PM->add(new PostDominatorTree());
    PM->add(new PostDominanceFrontier());
    PM->add(new LoopInfoWrapperPass());
    PM->add(new DetectParametersPass());
    PM->add(new StackAccessPass());

    Slicer *slicer = new Slicer();
    PM->add(slicer);

    PM->run(*Mod);


    if (OutputFilename.empty())
        Mod->dump();
    else {
        std::error_code EC;
        std::unique_ptr<tool_output_file> FDOut = llvm::make_unique<tool_output_file>(OutputFilename, EC,
                                                                                      sys::fs::F_None);
        if (EC) {
            errs() << EC.message() << '\n';
            return -1;
        }

        FDOut->os() << *Mod;

        FDOut->keep();
    }

    return 0;
}
