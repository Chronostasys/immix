/*
  Some LLVM passes helpful for
  integrating immix with LLVM
*/

#include "llvm/IR/PassManager.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
using namespace llvm;
namespace
{
  void immixPassLogic(Module &M);
  // The new pass manager plugin
  class ImmixPass : public PassInfoMixin<ImmixPass>
  {
    static char ID;

  public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };
  PreservedAnalyses ImmixPass::run(Module &M, ModuleAnalysisManager &AM)
  {
    immixPassLogic(M);
    return PreservedAnalyses::all();
  }

  /*
    This pass helps integrate immix with LLVM.

    It does the following:
    - Sets the GC name to "statepoint-example" for all functions. 
      TODO: current llvm-16 does not support custom gc strategy using
      RewriteStatepointsForGC pass. So we need to use the default gc strategy.
    - Adds a call to immix_gc_init in the global constructor
    - Adds a global variable declaration for the module stack map if the main function is present.

    However, it does not generate the stack map. This is done by the
    immix compiler plugin.

    Also note that mauch more work is needed to get immix working with
    LLVM. Besides the pass, you need to:
    - Implement visit functions for all complex types
    - replace all malloc calls with immix::alloc
    ...
  */
  void immixPassLogic(Module &M)
  {
    auto isMain = false;
    for (auto FB = M.functions().begin(), FE = M.functions().end(); FB != FE; ++FB)
    {
      Function *FV = &*FB;
      if (FV->getName() == "main")
      {
        isMain = true;
      }
      if (!FV->getName().ends_with("visitorf@") && !FV->getName().starts_with("llvm"))
      {
        FV->setGC("statepoint-example");
      }
      
    }
    if (isMain)
    {
      // auto gc_init_c = M.getOrInsertFunction("__gc_init_stackmap", Type::getVoidTy(M.getContext()));
      auto immix_init_c = M.getOrInsertFunction("immix_gc_init", Type::getVoidTy(M.getContext()), PointerType::get(IntegerType::get(M.getContext(), 8), 0));
      auto immix_init_f = cast<Function>(immix_init_c.getCallee());
      immix_init_f->setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
      SmallVector<Type *, 1> argTypes;
      argTypes.push_back(PointerType::get(IntegerType::get(M.getContext(), 8), 0));
      std::string symbol;
      // mac's symbol name has only one underscore
      #ifdef __APPLE__ 
      symbol += "_LLVM_StackMaps";
      #else
      symbol += "__LLVM_StackMaps";
      #endif
      // symbol += M.getSourceFileName();
      auto g = M.getOrInsertGlobal(symbol, Type::getInt8Ty(M.getContext()));
      GlobalVariable *g_c = cast<GlobalVariable>(g);
      
      g_c->setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
      g_c->setDSOLocal(true);
      g_c->setConstant(true);
      // g_c->setSection("__llvm_stackmaps");
      g_c->setAlignment(llvm::Align(4));
      // M.appendModuleInlineAsm(".globl __LLVM_StackMaps");
      // auto g = M.getNamedGlobal(symbol);
      SmallVector<Value *, 1> assertArgs;
      assertArgs.push_back(g);
      Function *gc_init_f;
      std::tie(gc_init_f, std::ignore) = createSanitizerCtorAndInitFunctions(M, "__gc_init_stackmap", "immix_gc_init", argTypes, assertArgs);
      gc_init_f->setLinkage(GlobalValue::LinkageTypes::InternalLinkage);
      // appendToCompilerUsed(M, gc_init_f);
      appendToGlobalCtors(M, gc_init_f, 1000);
    }
    
  }

  // The old pass manager plugin
  struct ImmixLegacy : public ModulePass
  {
    static char ID;
    ImmixLegacy() : ModulePass(ID) {}

    bool runOnModule(Module &M) override
    {
      immixPassLogic(M);

      return true;
    }
  };
}

// char ImmixPass::ID = 0;
char ImmixLegacy::ID = 0;
static RegisterPass<ImmixLegacy> X("plimmix", "plimmix gc Pass",
                                   false /* Only looks at CFG */,
                                   false /* Analysis Pass */);
