#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct DynCorrPredicatePass : llvm::PassInfoMixin<DynCorrPredicatePass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunDynCorrPredicate(llvm::Module& m);

extern llvm::cl::opt<bool> DynCorrPredicateEnable;