/*
  Some LLVM passes helpful for
  integrating immix with LLVM
*/

#include "llvm/IR/PassManager.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Attributes.h"

#include <iostream>
using namespace llvm;
namespace
{
  static bool IsREPL;
  extern "C" void setREPL(int isREPL)
  {
    IsREPL = isREPL == 1;
  }
  void immixPassLogic(Module &M);

  class ReplaceMallocPass : public PassInfoMixin<ReplaceMallocPass>
  {

  public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
  };
  PreservedAnalyses ReplaceMallocPass::run(Function &F, FunctionAnalysisManager &FAM)
  {
    // add function declare DioGC__malloc
    auto M = F.getParent();
    if (!M->getFunction("DioGC__malloc"))
    {
      // Generate DioGC__malloc function declaration
      FunctionType *DioGC__mallocType = FunctionType::get(
          PointerType::get(IntegerType::get(M->getContext(), 8), 1),
          {IntegerType::get(M->getContext(), 64), IntegerType::get(M->getContext(), 8), IntegerType::get(M->getContext(), 64)},
          false);
      Function *DioGC__mallocFunc = Function::Create(
          DioGC__mallocType,
          GlobalValue::LinkageTypes::ExternalLinkage,
          "DioGC__malloc",
          M);
    }

    /*
      replace all
      %2 = call ptr @malloc(i64 noundef %size)
      to
      %rsp = call ptr asm alignstack "mov $0, sp", "=r"() #0
      %rspi = ptrtoint ptr %rsp to i64
      %2 = call ptr @DioGC__malloc(i64 noundef %size, i8 4, i64 %rspi)
    */

    auto CIS = std::vector<Instruction *>();
    for (BasicBlock &BB : F)
    {
      for (Instruction &I : BB)
      {
        if (CallInst *CI = dyn_cast<CallInst>(&I))
        {
          Function *Callee = CI->getCalledFunction();
          if (Callee && Callee->getName() == "malloc")
          {
            // Create the new function call
            Function *NewCallee = M->getFunction("DioGC__malloc");

            // Create the new arguments
            std::vector<Value *> NewArgs;
            NewArgs.push_back(CI->getArgOperand(0));                                  // size
            NewArgs.push_back(ConstantInt::get(Type::getInt8Ty(M->getContext()), 4)); // i8 4
            // Add the stack pointer
            InlineAsm *SPAsm;
#if defined(__aarch64__)
            SPAsm = InlineAsm::get(FunctionType::get(PointerType::get(M->getContext(), 0), false),
                                   "mov $0, sp", "=r", true, InlineAsm::AsmDialect::AD_ATT);
#elif defined(__x86_64__)
            SPAsm = InlineAsm::get(FunctionType::get(PointerType::get(M->getContext(), 0), false),
                                   "mov %rsp, $0", "=r", true, InlineAsm::AsmDialect::AD_ATT);
#elif defined(_WIN64)
            SPAsm = InlineAsm::get(FunctionType::get(PointerType::get(M->getContext(), 0), false),
                                   "mov %rsp, $0", "=r", true, InlineAsm::AsmDialect::AD_ATT);
#else
#error "Unsupported architecture"
#endif
            // asm add attr: "gc-leaf-function"
            CallInst *SP = CallInst::Create(SPAsm, "", CI);
            SP->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::get(M->getContext(), "gc-leaf-function"));
            // convert to i64
            auto *RSPInt = new PtrToIntInst(SP, IntegerType::get(M->getContext(), 64), "", CI);
            NewArgs.push_back(RSPInt);

            // Create the new call instruction
            CallInst *NewCI = CallInst::Create(NewCallee, NewArgs, "", CI);

            // Replace the old call instruction with the new one
            CI->replaceAllUsesWith(NewCI);
            // CI->eraseFromParent();
            CIS.push_back(CI);
          }

          // remove all free calls
          if (Callee && Callee->getName() == "free")
          {
            CIS.push_back(CI);
          }
        }
      }
    }
    for (auto *CI : CIS)
    {
      CI->eraseFromParent();
    }
    return PreservedAnalyses::none();
  }

  // The new pass manager plugin
  class ImmixPass : public PassInfoMixin<ImmixPass>
  {
    static char ID;

  public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  };
  PreservedAnalyses ImmixPass::run(Module &M, ModuleAnalysisManager &AM)
  {
    // printf("running immix pass\n");
    immixPassLogic(M);
    return PreservedAnalyses::none();
  }

  /*
    # An escape analysis pass

    This pass would find any gc heap allocation of `Ordinary` type that's
    not necessary and replace them with stack allocation.

    ## About `Ordinary` type

    In most cases, types that size can be known at compile time are `Ordinary`. For example, a struct
  */
  class EscapePass : public PassInfoMixin<EscapePass>
  {
    static char ID;
    bool escaped;
    bool check_phi;

  public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    void correctPhi(llvm::iterator_range<llvm::Value::use_iterator> &uses, llvm::IRBuilder<> &builder, llvm::Module &M, std::__1::vector<llvm::PHINode *> &phis);
    void hasPhi(llvm::iterator_range<llvm::Value::use_iterator> &uses, bool &skip, int level);
    void replaceCallArgsAddrspaces(llvm::User *U, llvm::IRBuilder<> &builder, llvm::Value *alloca, llvm::Module &M, std::vector<llvm::MemSetInst *> &memsets, std::vector<llvm::CallInst *> &calls);
    /*
      Regenerate the gep instructions with new address space
    */
    void replace_geps(llvm::iterator_range<llvm::Value::user_iterator> &users, llvm::IRBuilder<> &builder, llvm::Value *alloca, std::vector<llvm::GetElementPtrInst *> &geps, llvm::Module &M, std::vector<llvm::MemSetInst *> &memsets, std::vector<llvm::CallInst *> &calls);
    bool are_phis_replacable(llvm::iterator_range<llvm::Value::use_iterator> &uses, int level);
    bool is_replacable(llvm::Value *value);
    bool replaceNocapturedParams(Function &F);
    EscapePass() : escaped(false) {}
    EscapePass(bool escaped, bool check_phi) : escaped(escaped), check_phi(check_phi) {}
  };

  PreservedAnalyses EscapePass::run(Module &M, ModuleAnalysisManager &AM)
  {
    IRBuilder<> builder(M.getContext());

    if (check_phi)
    {
      std::vector<Function *> functions;

      // find all functions which parameters has metadata nocapture and "pl_ordinary"
      for (auto FB = M.functions().begin(), FE = M.functions().end(); FB != FE; ++FB)
      {
        Function *FV = &*FB;
        if (!FV->getName().ends_with("visitorf@") && !FV->getName().starts_with("llvm") && !FV->isDeclaration())
        {
          functions.push_back(FV);
        }
      }
      for (auto *F : functions)
      {
        replaceNocapturedParams(*F);
      }
    }
    

    bool changed = true;
    int count = 0;
    while (changed)
    {

      changed = false;
      std::vector<CallInst *> mallocs;
      std::vector<llvm::CallInst *> calls;
      std::vector<PHINode *> phis;
      std::vector<AllocaInst *> allocas;
      std::vector<GetElementPtrInst *> geps;
      std::vector<MemSetInst *> memsets;
      std::vector<AddrSpaceCastInst *> addrspaces;
      // find all gc atomic type allocations, analysis to get non-escaped set.
      for (auto FB = M.functions().begin(), FE = M.functions().end(); FB != FE; ++FB)
      {
        Function *FV = &*FB;
        if (!FV->getName().ends_with("visitorf@") && !FV->getName().starts_with("llvm") && !FV->isDeclaration())
        {
          // doing escape analysis
          for (auto &BB : *FV)
          {
            for (auto &I : BB)
            {

              if (auto cast = dyn_cast<AddrSpaceCastInst>(&I))
              {
                // check if dst and src address space is same, if so add to delete list
                if (cast->getDestAddressSpace() == cast->getSrcAddressSpace())
                {
                  // change all uses to src address space
                  cast->replaceAllUsesWith(cast->getOperand(0));
                  addrspaces.push_back(cast);
                }
              }
              
              // if it's a call instruction and has pl_ordinary attribute
              if (auto *call = dyn_cast<CallInst>(&I))
              {
                if (auto *F = call->getCalledFunction())
                {
                  auto attrs = call->getAttributes();
                  if (!F->getName().equals("DioGC__malloc"))
                  {
                    continue;
                  }
                  auto * ty = call->getArgOperand(1);
                  if (!isa<ConstantInt>(ty) || !detail::isPresent(ty))
                  {
                    // if the size is not a constant, we can't replace it with alloca
                    continue;
                  }
                  auto *tyValue = dyn_cast<ConstantInt>(ty);
                  auto tyInt = tyValue->getZExtValue();
                  if (!attrs.hasRetAttr("pl_ordinary") && tyInt != 0)
                  {
                    continue;
                  }

                  if (!PointerMayBeCaptured(call, true, false))
                  {

                    auto info = attrs.getRetAttrs().getAttribute("pl_ordinary").getValueAsString();
                    if (info.size() > 0 && this->escaped)
                    {
                      printf("variable moved to stack: %s\n", info.str().c_str());
                    }

                    // if the pointer may be captured, then we change this gc malloc
                    // to stack alloca

                    // the first argument of gc malloc is the size
                    auto *size = call->getArgOperand(0);

                    if (!isa<ConstantInt>(size) || !detail::isPresent(size))
                    {
                      // if the size is not a constant, we can't replace it with alloca
                      continue;
                    }
                    auto uses = call->uses();
                    if (check_phi)
                    {
                      auto skip = false;
                      hasPhi(uses, skip,100);
                      if (skip)
                      {
                        continue;
                      }

                      if (!EscapePass::are_phis_replacable(uses, 0))
                      {
                        continue;
                      }
                    }

                    // size is a number, get it's value
                    auto *sizeValue = dyn_cast<ConstantInt>(size);
                    auto sizeInt = sizeValue->getZExtValue();
                    // get the size value

                    // replace it with alloca
                    builder.SetInsertPoint(&FV->front().front());
                    auto &alloca = *builder.CreateAlloca(ArrayType::get(IntegerType::get(M.getContext(), 8), sizeInt));
                    if (sizeInt >= 16)
                    {
                      alloca.setAlignment(llvm::Align(16));
                    }
                    else
                    {
                      alloca.setAlignment(llvm::Align(8));
                    }
                    alloca.takeName(call);

                    // find all gep, replace address space with 0
                    auto users = call->users();
                    replace_geps(users, builder, &alloca, geps, M, memsets, calls);

                    call->replaceAllUsesWith(&alloca);
                    // find all memset, regenrate memset
                    auto users1 = alloca.users();
                    for (auto *U : users1)
                    {
                      replaceCallArgsAddrspaces(U, builder, &alloca, M, memsets, calls);
                    }
                    allocas.push_back(&alloca);

                    mallocs.push_back(call);
                    changed = true;
                  }
                }
              }
            }
          }
        }
      }

      // There's a special case where `replaceAllUsesWith` won't cover:
      // Some LLVM pass would generate phi node, which may contians
      // non-escaped values. `replaceAllUsesWith` won't replace value after phi,
      // so we need to manually correct it.
      //
      // As phi is generated by pass, we can assume that the input values
      // must have same escape state.
      for (auto *alloca : allocas)
      {
        // correect phi
        auto uses = alloca->uses();
        correctPhi(uses, builder, M, phis);
      }
      // delete previous nodes.
      for (auto *call : mallocs)
      {
        call->eraseFromParent();
      }
      for (auto *phi : phis)
      {
        if (phi->getParent())
        {
          phi->eraseFromParent();
        }
      }
      for (auto *gep : geps)
      {
        if (gep->getParent())
        {
          gep->eraseFromParent();
        }
      }
      for (auto *memset : memsets)
      {
        if (memset->getParent())
        {
          memset->eraseFromParent();
        }
      }
      for (auto FB = M.functions().begin(), FE = M.functions().end(); FB != FE; ++FB)
      {
        Function *FV = &*FB;
        if (!FV->getName().ends_with("visitorf@") && !FV->getName().starts_with("llvm") && !FV->isDeclaration())
        {
          // if (check_phi)
          // {
          //   printf("function %s\n", FV->getName().str().c_str());
          // }

          // doing escape analysis
          for (auto &BB : *FV)
          {
            for (auto &I : BB)
            {
              if (auto *alloca = dyn_cast<AllocaInst>(&I))
              {
                auto users = alloca->users();
                for (auto *U : users)
                {
                  replaceCallArgsAddrspaces(U, builder, alloca, M, memsets, calls);
                }
              }
              if (auto *alloca = dyn_cast<GetElementPtrInst>(&I))
              {
                // check addrspace is 0
                if (alloca->getPointerAddressSpace() == 0)
                {
                  auto users = alloca->users();
                  for (auto *U : users)
                  {
                    replaceCallArgsAddrspaces(U, builder, alloca, M, memsets, calls);
                  }
                }
              }
            }
          }
        }
      }
      for (auto *call : calls)
      {
        if (call->getParent())
        {
          call->replaceAllUsesWith(call);
        }
      }
      for (auto *address : addrspaces)
      {
        if (address->getParent())
        {
          address->eraseFromParent();
        }
      }
    }
    return PreservedAnalyses::none();
  }

  void EscapePass::correctPhi(llvm::iterator_range<llvm::Value::use_iterator> &uses, llvm::IRBuilder<> &builder, llvm::Module &M, std::vector<llvm::PHINode *> &phis)
  {
    while (true)
    {
      auto noMorePhi = true;
      for (auto &U : uses)
      {

        auto *user = U.getUser();
        // if it's phi
        if (auto *phi = dyn_cast<PHINode>(user))
        {
          noMorePhi = false;
          // build a new phi which address space is 0
          builder.SetInsertPoint(phi->getParent()->getFirstNonPHI());
          auto newphi = builder.CreatePHI(PointerType::get(IntegerType::get(M.getContext(), 8), 0), phi->getNumIncomingValues());
          for (unsigned i = 0; i < phi->getNumIncomingValues(); i++)
          {
            auto *incoming = phi->getIncomingValue(i);
            auto *incomingBlock = phi->getIncomingBlock(i);
            newphi->addIncoming(incoming, incomingBlock);
          }
          phi->replaceAllUsesWith(newphi);
          phis.push_back(phi);
          // printf("replaced phi\n");
          uses = newphi->uses();
        }
      }
      if (noMorePhi)
      {
        break;
      }
    }
  }

  void EscapePass::hasPhi(llvm::iterator_range<llvm::Value::use_iterator> &uses, bool &skip, int level)
  {
    if (!are_phis_replacable(uses,level))
    {
      skip = true;
      return;
    }
    for (auto &U : uses)
    {
      auto *user = U.getUser();
      // if it's phi
      // if (auto *phi = dyn_cast<PHINode>(user))
      // {
      //   skip = true;
      //   break;
      // }
      if (auto *call = dyn_cast<CallInst>(user))
      {
        // check if function's corresponding argument type is address space 1 pointer
        auto *F = call->getFunctionType();
        if (F)
        {
          auto arg = call->getOperand(U.getOperandNo())->getType();
          if (arg->isPointerTy() && arg->getPointerAddressSpace() == 1)
          {
            skip = true;
            break;
          }
        }
        
      }
      //  if (!is_replacable(user))
      // {
      //   skip = true;
      //   break;
      // }
      
      if (auto *gep = dyn_cast<GetElementPtrInst>(user))
      {
        auto uses = gep->uses();
        hasPhi(uses, skip,level);
      }
      if (skip == true)
      {
        break;
      }
      
    }
  }

  void EscapePass::replaceCallArgsAddrspaces(llvm::User *U, llvm::IRBuilder<> &builder, llvm::Value *alloca, llvm::Module &M, std::vector<llvm::MemSetInst *> &memsets, std::vector<llvm::CallInst *> &calls)
  {
    if (auto *memset = dyn_cast<MemSetInst>(U))
    {
      auto *dest = memset->getDest();
      auto *len = memset->getLength();
      auto *value = memset->getValue();
      builder.SetInsertPoint(memset);

      auto *newmemset = builder.CreateMemSet(alloca, value, len, memset->getDestAlign(), memset->isVolatile());
      memset->replaceAllUsesWith(newmemset);
      memsets.push_back(memset);
    }

  }

  void EscapePass::replace_geps(llvm::iterator_range<llvm::Value::user_iterator> &users, llvm::IRBuilder<> &builder, llvm::Value *ptr, std::vector<llvm::GetElementPtrInst *> &geps, llvm::Module &M, std::vector<llvm::MemSetInst *> &memsets, std::vector<llvm::CallInst *> &calls)
  {
    for (auto *U : users)
    {
      if (auto *gep = dyn_cast<GetElementPtrInst>(U))
      {
        std::vector<Value *> arr;
        // Value *v = nullptr;
        for (unsigned i = 0; i < gep->getNumOperands(); ++i)
        {
          if (i == 0)
          {
            // first operand is the pointer, skip it. we only need index
            continue;
          }

          arr.push_back(gep->getOperand(i));
        }
        builder.SetInsertPoint(gep);
        auto *newgep = builder.CreateGEP(gep->getSourceElementType(), ptr, arr, gep->getName(), gep->isInBounds());
        auto newusers = gep->users();
        for (auto *U : newusers)
        {
          replaceCallArgsAddrspaces(U, builder, newgep, M, memsets, calls);
        }
        replace_geps(newusers, builder, newgep, geps, M, memsets, calls);
        gep->replaceAllUsesWith(newgep);
        // gep->eraseFromParent();
        geps.push_back(gep);
      }
    }
  }

  bool EscapePass::is_replacable(llvm::Value *value)
  {
    // if it's a call instruction and has pl_ordinary attribute
    if (auto *call = dyn_cast<CallInst>(value))
    {
      if (auto *F = call->getCalledFunction())
      {
        auto attrs = call->getAttributes();
        // if (!attrs.hasRetAttr("pl_ordinary"))
        // {
        //   return false;
        // }
        if (!F->getName().equals("DioGC__malloc"))
        {
          return false;
        }

        if (!PointerMayBeCaptured(call, true, false))
        {

          auto info = attrs.getRetAttrs().getAttribute("pl_ordinary").getValueAsString();

          // if the pointer may be captured, then we change this gc malloc
          // to stack alloca

          // the first argument of gc malloc is the size
          auto *size = call->getArgOperand(0);

          if (!isa<ConstantInt>(size) || !detail::isPresent(size))
          {
            // if the size is not a constant, we can't replace it with alloca
            return false;
          }
          auto * ty = call->getArgOperand(1);
          if (!isa<ConstantInt>(ty) || !detail::isPresent(ty))
          {
            // if the size is not a constant, we can't replace it with alloca
            return false;
          }
          auto *tyValue = dyn_cast<ConstantInt>(ty);
          auto tyInt = tyValue->getZExtValue();
          if (!attrs.hasRetAttr("pl_ordinary") && tyInt != 0)
          {
            return false;
          }
          return true;
        }
      }
    }
    if (auto * arg = dyn_cast<Argument>(value))
    {
      auto thisattr = arg->getParent()->getAttributes().getParamAttrs(arg->getArgNo());
      if (thisattr.hasAttribute(Attribute::NoCapture) && thisattr.hasAttribute("pl_ordinary") && arg->getType()->isPointerTy())
      {
        return true;
      }
    }
    
    return false;
  }

  bool EscapePass::replaceNocapturedParams(Function &F)
  {
    auto M = F.getParent();
      IRBuilder<> builder(M->getContext());
      std::vector<CallInst *> mallocs;
      std::vector<llvm::CallInst *> calls;
      std::vector<PHINode *> phis;
      std::vector<AllocaInst *> allocas;
      std::vector<GetElementPtrInst *> geps;
      std::vector<MemSetInst *> memsets;
    // assert(F.getFunctionType()->isVarArg() && "Function isn't varargs!");
    if (F.isDeclaration())
      return false;
    auto found = false;
    auto attr = F.getAttributes();
    std::vector<bool> replacable;
    for (auto &arg : F.args())
    {
      auto thisattr = attr.getParamAttrs(arg.getArgNo());
          auto uses = arg.uses();
          auto skip = false;
          hasPhi(uses, skip,100);
      if (thisattr.hasAttribute(Attribute::NoCapture) && thisattr.hasAttribute("pl_ordinary") && arg.getType()->getPointerAddressSpace() == 1 && arg.getType()->isPointerTy()&&are_phis_replacable(uses, 100) &&!skip)
      {
        found = true;
        replacable.push_back(true);
      }else {
        replacable.push_back(false);
      }
    }
    if (!found)
    {
      return false;
    }
    

    // // Ensure that the function is only directly called.
    // if (F.hasAddressTaken())
    //   return false;

    // Don't touch naked functions. The assembly might be using an argument, or
    // otherwise rely on the frame layout in a way that this analysis will not
    // see.
    if (F.hasFnAttribute(Attribute::Naked))
    {
      return false;
    }



    // If we get here, there are no calls to llvm.vastart in the function body,
    // remove the "..." and adjust all the calls.

    // Start by computing a new prototype for the function, which is the same as
    // the old function, but param addressespace is 0
    FunctionType *FTy = F.getFunctionType();

    std::vector<Type *> Params;
    // for FTy->param_begin(), FTy->param_end()
    for (FunctionType::param_iterator I = FTy->param_begin(), E = FTy->param_end();
         I != E; ++I)
    {
      if (replacable[I - FTy->param_begin()])
      {
        if ((*I)->getPointerAddressSpace() == 1)
        {
          Params.push_back(PointerType::get((*I), 0));
        }else
        {
          Params.push_back(*I);
        }
        
      }
      else
      {
        Params.push_back(*I);
      }
    }
    FunctionType *NFTy = FunctionType::get(FTy->getReturnType(), Params, FTy->isVarArg());

    // Create the new function body and insert it into the module...
    Function *NF = Function::Create(NFTy, F.getLinkage(), F.getAddressSpace());
    NF->copyAttributesFrom(&F);
    NF->setComdat(F.getComdat());
    F.getParent()->getFunctionList().insert(F.getIterator(), NF);
    NF->takeName(&F);
    NF->IsNewDbgInfoFormat = F.IsNewDbgInfoFormat;

    // Loop over all the callers of the function, transforming the call sites
    // to pass in a smaller number of arguments into the new function.
    //
    std::vector<Value *> Args;
    for (User *U : llvm::make_early_inc_range(F.users()))
    {
      CallBase *CB = dyn_cast<CallBase>(U);
      if (!CB)
        continue;

      // Pass all the same arguments, change replacable arguments to address space 0
      // (by performing a addressspacecast). remove tail/must tail hint, as we may pass allocas as args https://llvm.org/docs/LangRef.html#id332
      // for CB->arg_begin(), CB->arg_end()
      for (auto I = CB->arg_begin(), E = CB->arg_end();
           I != E; ++I)
      {
        if (replacable[I - CB->arg_begin()])
        {
          if ((*I)->getType()->isPointerTy() && (*I)->getType()->getPointerAddressSpace() == 1)
          {
            Args.push_back(new AddrSpaceCastInst(*I, PointerType::get((*I)->getType(), 0), "", CB));
          }else {
            Args.push_back(*I);
          }
        }
        else
        {
          Args.push_back(*I);
        }
      }

      // Drop any attributes that were on the vararg arguments.
      AttributeList PAL = CB->getAttributes();
      if (!PAL.isEmpty())
      {
        SmallVector<AttributeSet, 8> ArgAttrs;
        for (unsigned ArgNo = 0; ArgNo < CB->arg_size(); ++ArgNo)
          ArgAttrs.push_back(PAL.getParamAttrs(ArgNo));
        PAL = AttributeList::get(F.getContext(), PAL.getFnAttrs(),
                                 PAL.getRetAttrs(), ArgAttrs);
      }

      SmallVector<OperandBundleDef, 1> OpBundles;
      CB->getOperandBundlesAsDefs(OpBundles);

      CallBase *NewCB = nullptr;
      if (InvokeInst *II = dyn_cast<InvokeInst>(CB))
      {
        NewCB = InvokeInst::Create(NF, II->getNormalDest(), II->getUnwindDest(),
                                   Args, OpBundles, "", CB);
      }
      else
      {
        NewCB = CallInst::Create(NF, Args, OpBundles, "", CB);
        cast<CallInst>(NewCB)->setTailCallKind(
            CallInst::TCK_None); // Drop the tail call hint.
      }
      NewCB->setCallingConv(CB->getCallingConv());
      NewCB->setAttributes(PAL);
      NewCB->copyMetadata(*CB, {LLVMContext::MD_prof, LLVMContext::MD_dbg});

      Args.clear();

      if (!CB->use_empty())
        CB->replaceAllUsesWith(NewCB);

      NewCB->takeName(CB);
          // NewCB->print(errs());
          // errs() << "\n";

      // Finally, remove the old call from the program, reducing the use-count of
      // F.
      CB->eraseFromParent();
    }


      // Function::arg_iterator I2 = NF->arg_begin();
      // for (Argument &Arg : F.args()) {
      //   Arg.replaceAllUsesWith(&*I2);
      //   I2->takeName(&Arg);
      //   ++I2;
      // }
    // Since we have now created the new function, splice the body of the old
    // function right into the new function, leaving the old rotting hulk of the
    // function empty.
    NF->splice(NF->begin(), &F);


    // Loop over the argument list, transferring uses of the old arguments over to
    // the new arguments, also transferring over the names as well.  While we're
    // at it, remove the dead arguments from the DeadArguments list.
    for (Function::arg_iterator I = F.arg_begin(), E = F.arg_end(),
                                I2 = NF->arg_begin();
         I != E; ++I, ++I2)
    {
      // Move the name and users over to the new version.
      I->replaceAllUsesWith(&*I2);
      I2->takeName(&*I);
      if (replacable[I - F.arg_begin()])
      {
        auto users = I2->users();
        replace_geps(users, builder, &*I2, geps, *M, memsets, calls);
        auto uses = I2->uses();
        correctPhi(uses, builder, *M, phis);
        for (auto *U : users)
        {
          replaceCallArgsAddrspaces(U, builder, &*I2, *M, memsets, calls);
        }
      }
      
    }

    // Clone metadata from the old function, including debug info descriptor.
    SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
    F.getAllMetadata(MDs);
    for (auto [KindID, Node] : MDs)
      NF->addMetadata(KindID, *Node);

    // Fix up any BlockAddresses that refer to the function.
    F.replaceAllUsesWith(NF);
    // Delete the bitcast that we just created, so that NF does not
    // appear to be address-taken.
    NF->removeDeadConstantUsers();
    // Finally, nuke the old function.
    F.eraseFromParent();
    // NF->print(errs());
    //           errs() << "\n";
// delete previous nodes.
      for (auto *call : mallocs)
      {
        call->eraseFromParent();
      }
      for (auto *phi : phis)
      {
        if (phi->getParent())
        {
          phi->eraseFromParent();
        }
      }
      for (auto *gep : geps)
      {
        if (gep->getParent())
        {
          gep->eraseFromParent();
        }
      }
      for (auto *memset : memsets)
      {
        if (memset->getParent())
        {
          memset->eraseFromParent();
        }
      }
    return true;
  }

  bool EscapePass::are_phis_replacable(llvm::iterator_range<llvm::Value::use_iterator> &uses, int level)
  {
    if (level > 100)
    {
      return false;
    }

    while (true)
    {
      auto noMorePhi = true;
      for (auto &U : uses)
      {

        auto *user = U.getUser();
        // if it's phi
        if (auto *phi = dyn_cast<PHINode>(user))
        {
          noMorePhi = false;
          // check if each incoming value is capable of being replaced

          for (unsigned i = 0; i < phi->getNumIncomingValues(); i++)
          {
            auto *incoming = phi->getIncomingValue(i);

            if (!is_replacable(incoming))
            {
              return false;
            }
            auto uses = incoming->uses();
            if (!are_phis_replacable(uses, level + 1))
            {
              return false;
            }
          }

          // printf("replaced phi\n");
          uses = phi->uses();
        }
      }
      if (noMorePhi)
      {
        break;
      }
    }
    return true;
  }

  /*
    This pass helps integrate immix with LLVM.

    It does the following:
    - Sets the GC name to "plimmix" for all functions.
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
        FV->setGC("plimmix");
      }
    }
    if (IsREPL)
    {
      return;
    }

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
    if (!M.getFunction("__gc_init_stackmap"))
    {
      SmallVector<Value *, 1> assertArgs;
      assertArgs.push_back(g);
      Function *gc_init_f;
      std::tie(gc_init_f, std::ignore) = createSanitizerCtorAndInitFunctions(M, "__gc_init_stackmap", "immix_gc_init", argTypes, assertArgs);
      gc_init_f->setLinkage(GlobalValue::LinkageTypes::LinkOnceAnyLinkage);
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

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
// This part is the new way of registering your pass
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo()
{
  return {
      LLVM_PLUGIN_API_VERSION, "PLImmix", "v0.1",
      [](PassBuilder &PB)
      {
        PB.registerPipelineParsingCallback(
            [](StringRef Name, FunctionPassManager &FPM,
               ArrayRef<PassBuilder::PipelineElement>)
            {
              if (Name == "replace-malloc")
              {
                FPM.addPass(ReplaceMallocPass());
                return true;
              }
              return false;
            });
        PB.registerPipelineParsingCallback(
            [](StringRef Name, ModulePassManager &MPM,
               ArrayRef<PassBuilder::PipelineElement>)
            {
              if (Name == "plimmix")
              {
                MPM.addPass(ImmixPass());
                return true;
              }
              return false;
            });
        PB.registerPipelineParsingCallback(
            [](StringRef Name, ModulePassManager &MPM,
               ArrayRef<PassBuilder::PipelineElement>)
            {
              if (Name == "pl-escape")
              {
                MPM.addPass(EscapePass());
                return true;
              }
              return false;
            });
      }};
}