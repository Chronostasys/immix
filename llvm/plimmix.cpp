// #include "llvm/CodeGen/GCStrategy.h"
#include "llvm/IR/GCStrategy.h"
#include "llvm/IR/BuiltinGCs.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/Compiler.h"
#include "plimmixprinter.cpp"
#include "plimmix_pass.cpp"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/Vectorize/LoopVectorize.h"
#include "llvm/Transforms/Vectorize/SLPVectorizer.h"
#include "llvm/Transforms/Vectorize/LoadStoreVectorizer.h"
#include "llvm/Transforms/Vectorize/VectorCombine.h"
#include "llvm/Transforms/IPO/ForceFunctionAttrs.h"
#include "llvm/Transforms/IPO/Attributor.h"
#include "llvm/Transforms/IPO/InferFunctionAttrs.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar/LoopDeletion.h"
#include "llvm/Transforms/Scalar/LoopRotation.h"
#include "llvm/Transforms/Scalar/LoopDistribute.h"
#include "llvm/Transforms/Scalar/RewriteStatepointsForGC.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"

#include "llvm-c/Types.h"
#include "llvm-c/BitWriter.h"
#include "llvm-c/Transforms/PassBuilder.h"
// #include "rewriteStatepointForGC.cpp"
#include "stripRelocationPass.cpp"

namespace
{
    /*
        This is the GC strategy for immix.
        It is used to register our immix GC with LLVM.
    */
    class LLVM_LIBRARY_VISIBILITY PLImmixGC : public GCStrategy
    {
    public:
        PLImmixGC()
        {
            UseStatepoints = true;
            UseRS4GC = true;
            // These options are all gc.root specific, we specify them so that the
            // gc.root lowering code doesn't run.
            NeededSafePoints = false;
            UsesMetadata = false;
        }

        std::optional<bool> isGCManagedPointer(const Type *Ty) const override {
            // Method is only valid on pointer typed values.
            const PointerType *PT = cast<PointerType>(Ty);
            return (1 == PT->getAddressSpace());


            // // conservative mark, we can return false for all pointers 
            // return false;
        }
    };

    GCRegistry::Add<PLImmixGC>
        X("plimmix", "pivot-lang immix garbage collector.");
}

extern "C" LLVMMemoryBufferRef parse_ir(char* ir)
{
    SMDiagnostic Err;
    auto Ctx = std::make_unique<LLVMContext>();
    auto sIr = std::string(ir);
    auto Mod = parseIRFile(sIr, Err, *Ctx);
    if (!Mod)
    {
        Err.print("immix", errs());
        return nullptr;
    }
    auto mb = LLVMWriteBitcodeToMemoryBuffer(wrap(Mod.release()));

    return mb;
}

extern "C" LLVMMemoryBufferRef parse_ir_string(char* ir)
{
    SMDiagnostic Err;
    auto Ctx = std::make_unique<LLVMContext>();
    auto sIr = std::string(ir);
    auto Mod = parseIR(MemoryBufferRef(*MemoryBuffer::getMemBuffer(sIr)), Err, *Ctx);
    if (!Mod)
    {
        Err.print("load ir err", errs());
        return nullptr;
    }
    auto mb = LLVMWriteBitcodeToMemoryBuffer(wrap(Mod.release()));

    return mb;
}


extern "C" void LLVMLinkPLImmixGC()
{
    linkAllBuiltinGCs();
}

extern "C" void add_module_pass(llvm::legacy::PassManagerBase *PB) {
    PB->add(new ImmixLegacy());

}
#include "llvm/ADT/StringExtras.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/Support/TargetSelect.h"

/*
    param: opt opt level

    The new LLVM Pass Manager does not have official C bindings yet.
    So we have to write one ourselves.
*/
extern "C" void run_module_pass(LLVMModuleRef  M, int opt, int debug, int print_escaped) {
//     InitializeNativeTarget();
// //   Initialize();
//     std::string CPUStr, FeaturesStr;
//     Triple ModuleTriple(unwrap(M)->getTargetTriple());
//     std::string Error;
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();
    auto TargetTriple = sys::getDefaultTargetTriple();
    std::string Error;
    auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);

//     auto target = TargetRegistry::lookupTarget(ModuleTriple.getTriple(), Error);
//     CPUStr = sys::getHostCPUName();
//     FeaturesStr = getFeaturesStr();
//     // codegen::setFunctionAttributes(CPUStr, FeaturesStr, *unwrap(M));
    TargetOptions Options = TargetOptions();
    Options.UnsafeFPMath = true;
    Options.NoNaNsFPMath = true;
    Options.ApproxFuncFPMath = true;
    Options.NoTrappingFPMath = true;
    Options.AllowFPOpFusion = FPOpFusion::Fast;

    auto O = OptimizationLevel::O2;
//     auto COpt = CodeGenOpt::Default;
//     switch (opt)
//     {
//     case 0:
//         COpt = CodeGenOpt::None;
//         break;
//     case 1:
//         COpt = CodeGenOpt::Less;
//         break;
//     case 2:
//         COpt = CodeGenOpt::Default;
//         break;
//     case 3:
//         COpt = CodeGenOpt::Aggressive;
//         break;
//     default:
//         break;
//     }
//     auto TM = target->createTargetMachine(
//       ModuleTriple.getTriple(), CPUStr, FeaturesStr,
//       Options, Reloc::DynamicNoPIC,
//       std::nullopt, COpt);
    // These must be declared in this order so that they are destroyed in the
    // correct order due to inter-analysis-manager references.
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager CGAM;
    ModuleAnalysisManager MAM;

    PipelineTuningOptions PTO;
    PTO.LoopUnrolling = true;

    // Create the new pass manager builder.
    // Take a look at the PassBuilder constructor parameters for more
    // customization, e.g. specifying a TargetMachine or various debugging
    // options.
    auto CPU = "generic";
    auto Features = "";
    auto TargetMachine = Target->createTargetMachine(TargetTriple, CPU, Features, Options, Reloc::PIC_);
    PassBuilder PB(TargetMachine);

    AAManager AA = PB.buildDefaultAAPipeline();
    FAM.registerPass([&] { return std::move(AA); });
    // Register all the basic analyses with the managers.
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);


    ModulePassManager MPM;
    FunctionPassManager FPM;
    LoopPassManager LPM;
    CGSCCPassManager CGPM;
    MPM.addPass(EscapePass(print_escaped == 1,false));
    MPM.addPass(ImmixPass());
    switch (opt)
    {
    case 0:
        O = OptimizationLevel::O0;
        MPM.addPass(PB.buildO0DefaultPipeline(O));
        MPM.addPass(EscapePass(print_escaped == 1, true));
        MPM.addPass(AlwaysInlinerPass());
        break;
    case 1:
        O = OptimizationLevel::O1;
        MPM.addPass(PB.buildPerModuleDefaultPipeline(O));
        FPM = PB.buildFunctionSimplificationPipeline(O, ThinOrFullLTOPhase::None);
        MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
        MPM.addPass(EscapePass(print_escaped == 1, true));
        // PB.parsePassPipeline(MPM, "always-inline");
        MPM.addPass(AlwaysInlinerPass());
        break;
    case 2:
        O = OptimizationLevel::O2;
        MPM.addPass(PB.buildPerModuleDefaultPipeline(O));
        FPM = PB.buildFunctionSimplificationPipeline(O, ThinOrFullLTOPhase::None);
        MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
        MPM.addPass(EscapePass(print_escaped == 1, true));
        // PB.parsePassPipeline(MPM, "always-inline");
        MPM.addPass(AlwaysInlinerPass());
        break;
    case 3:
        O = OptimizationLevel::O3;
        FPM = PB.buildFunctionSimplificationPipeline(O, ThinOrFullLTOPhase::None);
        MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
        // MPM.addPass(PB.buildFatLTODefaultPipeline(
        //   O, true,
        //   true));
        MPM.addPass(PB.buildThinLTOPreLinkDefaultPipeline(O));
        // copied from llvm-opt's pipeline
        PB.parsePassPipeline(MPM, "annotation2metadata,forceattrs,inferattrs,coro-early,function<eager-inv>(lower-expect,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;no-switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,sroa<modify-cfg>,early-cse<>,callsite-splitting),openmp-opt,ipsccp,called-value-propagation,globalopt,function(mem2reg),function<eager-inv>(instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),require<globals-aa>,function(invalidate<aa>),require<profile-summary>,cgscc(devirt<4>(inline<only-mandatory>,inline,function-attrs,argpromotion,openmp-opt-cgscc,function<eager-inv>(sroa<modify-cfg>,early-cse<memssa>,speculative-execution,jump-threading,correlated-propagation,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,aggressive-instcombine<max-iterations=5>,libcalls-shrinkwrap,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,reassociate,require<opt-remark-emit>,loop-mssa(loop-instsimplify,loop-simplifycfg,licm<no-allowspeculation>,loop-rotate,licm<allowspeculation>,simple-loop-unswitch<nontrivial;trivial>),simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,loop(loop-idiom,indvars,loop-deletion,loop-unroll-full),sroa<modify-cfg>,vector-combine,mldst-motion<no-split-footer-bb>,gvn<>,sccp,bdce,instcombine<max-iterations=5>,jump-threading,correlated-propagation,adce,memcpyopt,dse,loop-mssa(licm<allowspeculation>),coro-elide,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;hoist-common-insts;sink-common-insts>,instcombine),coro-split)),deadargelim,coro-cleanup,globalopt,globaldce,elim-avail-extern,rpo-function-attrs,recompute-globalsaa,function<eager-inv>(float2int,lower-constant-intrinsics,loop(loop-rotate,loop-deletion),loop-distribute,inject-tli-mappings,loop-vectorize<no-interleave-forced-only;no-vectorize-forced-only;>,loop-load-elim,instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;forward-switch-cond;switch-range-to-icmp;switch-to-lookup;no-keep-loops;hoist-common-insts;sink-common-insts>,slp-vectorizer,vector-combine,instcombine<max-iterations=5>,loop-unroll<O3>,transform-warning,sroa<preserve-cfg>,instcombine<max-iterations=5>,require<opt-remark-emit>,loop-mssa(licm<allowspeculation>),alignment-from-assumptions,loop-sink,instsimplify,div-rem-pairs,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),globaldce,constmerge,cg-profile,rel-lookup-table-converter,function(annotation-remarks),verify");
        MPM.addPass(EscapePass(print_escaped == 1, true));
        PB.parsePassPipeline(MPM, "annotation2metadata,forceattrs,inferattrs,coro-early,always-inline,function<eager-inv>(lower-expect,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;no-switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,sroa<modify-cfg>,early-cse<>,callsite-splitting),openmp-opt,ipsccp,called-value-propagation,globalopt,function(mem2reg),function<eager-inv>(instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),require<globals-aa>,function(invalidate<aa>),require<profile-summary>,cgscc(devirt<4>(inline<only-mandatory>,inline,function-attrs,argpromotion,openmp-opt-cgscc,function<eager-inv>(sroa<modify-cfg>,early-cse<memssa>,speculative-execution,jump-threading,correlated-propagation,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,aggressive-instcombine<max-iterations=5>,libcalls-shrinkwrap,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,reassociate,require<opt-remark-emit>,loop-mssa(loop-instsimplify,loop-simplifycfg,licm<no-allowspeculation>,loop-rotate,licm<allowspeculation>,simple-loop-unswitch<nontrivial;trivial>),simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,loop(loop-idiom,indvars,loop-deletion,loop-unroll-full),sroa<modify-cfg>,vector-combine,mldst-motion<no-split-footer-bb>,gvn<>,sccp,bdce,instcombine<max-iterations=5>,jump-threading,correlated-propagation,adce,memcpyopt,dse,loop-mssa(licm<allowspeculation>),coro-elide,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;hoist-common-insts;sink-common-insts>,instcombine),coro-split)),deadargelim,coro-cleanup,globalopt,globaldce,elim-avail-extern,rpo-function-attrs,recompute-globalsaa,function<eager-inv>(float2int,lower-constant-intrinsics,loop(loop-rotate,loop-deletion),loop-distribute,inject-tli-mappings,loop-vectorize<no-interleave-forced-only;no-vectorize-forced-only;>,loop-load-elim,instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;forward-switch-cond;switch-range-to-icmp;switch-to-lookup;no-keep-loops;hoist-common-insts;sink-common-insts>,slp-vectorizer,vector-combine,instcombine<max-iterations=5>,loop-unroll<O3>,transform-warning,sroa<preserve-cfg>,instcombine<max-iterations=5>,require<opt-remark-emit>,loop-mssa(licm<allowspeculation>),alignment-from-assumptions,loop-sink,instsimplify,div-rem-pairs,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),globaldce,constmerge,cg-profile,rel-lookup-table-converter,function(annotation-remarks),verify");
        MPM.addPass(EscapePass(print_escaped == 1, true));
        PB.parsePassPipeline(MPM, "annotation2metadata,forceattrs,inferattrs,coro-early,always-inline,function<eager-inv>(lower-expect,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;no-switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,sroa<modify-cfg>,early-cse<>,callsite-splitting),openmp-opt,ipsccp,called-value-propagation,globalopt,function(mem2reg),function<eager-inv>(instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),require<globals-aa>,function(invalidate<aa>),require<profile-summary>,cgscc(devirt<4>(inline<only-mandatory>,inline,function-attrs,argpromotion,openmp-opt-cgscc,function<eager-inv>(sroa<modify-cfg>,early-cse<memssa>,speculative-execution,jump-threading,correlated-propagation,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,aggressive-instcombine<max-iterations=5>,libcalls-shrinkwrap,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,reassociate,require<opt-remark-emit>,loop-mssa(loop-instsimplify,loop-simplifycfg,licm<no-allowspeculation>,loop-rotate,licm<allowspeculation>,simple-loop-unswitch<nontrivial;trivial>),simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>,instcombine<max-iterations=5>,loop(loop-idiom,indvars,loop-deletion,loop-unroll-full),sroa<modify-cfg>,vector-combine,mldst-motion<no-split-footer-bb>,gvn<>,sccp,bdce,instcombine<max-iterations=5>,jump-threading,correlated-propagation,adce,memcpyopt,dse,loop-mssa(licm<allowspeculation>),coro-elide,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;hoist-common-insts;sink-common-insts>,instcombine),coro-split)),deadargelim,coro-cleanup,globalopt,globaldce,elim-avail-extern,rpo-function-attrs,recompute-globalsaa,function<eager-inv>(float2int,lower-constant-intrinsics,loop(loop-rotate,loop-deletion),loop-distribute,inject-tli-mappings,loop-vectorize<no-interleave-forced-only;no-vectorize-forced-only;>,loop-load-elim,instcombine<max-iterations=5>,simplifycfg<bonus-inst-threshold=1;forward-switch-cond;switch-range-to-icmp;switch-to-lookup;no-keep-loops;hoist-common-insts;sink-common-insts>,slp-vectorizer,vector-combine,instcombine<max-iterations=5>,loop-unroll<O3>,transform-warning,sroa<preserve-cfg>,instcombine<max-iterations=5>,require<opt-remark-emit>,loop-mssa(licm<allowspeculation>),alignment-from-assumptions,loop-sink,instsimplify,div-rem-pairs,tailcallelim,simplifycfg<bonus-inst-threshold=1;no-forward-switch-cond;switch-range-to-icmp;no-switch-to-lookup;keep-loops;no-hoist-common-insts;no-sink-common-insts>),globaldce,constmerge,cg-profile,rel-lookup-table-converter,function(annotation-remarks),verify");
        break;
    default:
        MPM.addPass(PB.buildPerModuleDefaultPipeline(O));
        FPM = PB.buildFunctionSimplificationPipeline(O, ThinOrFullLTOPhase::None);
        MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
        MPM.addPass(EscapePass(print_escaped == 1, true));
        // PB.parsePassPipeline(MPM, "always-inline");
        MPM.addPass(AlwaysInlinerPass());
        break;
    }
    MPM.addPass(RewriteStatepointsForGC());
    if (debug)
    {
        MPM.addPass(createModuleToFunctionPassAdaptor(PLStripGCRelocates()));
    }
    
    // Optimize the IR!
    MPM.run(*unwrap(M), MAM);


}


/*
    Shadow stack implementation for immix. (used in JIT mode, but may not work now)
*/
extern "C"
{
    /// The map for a single function's stack frame.  One of these is
    ///        compiled as constant data into the executable for each function.
    ///
    /// Storage of metadata values is elided if the %metadata parameter to
    /// @llvm.gcroot is null.
    struct FrameMap
    {
        int32_t NumRoots;    //< Number of roots in stack frame.
        int32_t NumMeta;     //< Number of metadata entries.  May be < NumRoots.
        const void *Meta[0]; //< Metadata for each root.
    };

    /// A link in the dynamic shadow stack.  One of these is embedded in
    ///        the stack frame of each function on the call stack.
    struct StackEntry
    {
        StackEntry *Next;    //< Link to next stack entry (the caller's).
        const FrameMap *Map; //< Pointer to constant FrameMap.
        void *Roots[0];      //< Stack roots (in-place array).
    };

    /// The head of the singly-linked list of StackEntries.  Functions push
    ///        and pop onto this in their prologue and epilogue.
    ///
    /// Since there is only a global list, this technique is not threadsafe.
    thread_local StackEntry **llvm_gc_root_chain;

    void SetShadowStackAddr(void *addr)
    {
        llvm_gc_root_chain = (StackEntry **)addr;
    }

    /// Calls Visitor(root, meta) for each GC root on the stack.
    ///        root and meta are exactly the values passed to
    ///        @llvm.gcroot.
    ///
    /// Visitor could be a function to recursively mark live objects.  Or it
    /// might copy them to another heap or generation.
    ///
    /// @param Visitor A function to invoke for every GC root on the stack.
    void visitGCRoots(void (*Visitor)(void **Root, const void *Meta))
    {
        for (StackEntry *R = *llvm_gc_root_chain; R; R = R->Next)
        {
            unsigned i = 0;

            // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
            for (unsigned e = R->Map->NumMeta; i != e; ++i)
            {
                Visitor(&R->Roots[i], R->Map->Meta[i]);
            }

            // For roots [NumMeta, NumRoots), the metadata pointer is null.
            for (unsigned e = R->Map->NumRoots; i != e; ++i)
            {
                Visitor(&R->Roots[i], NULL);
            }
        }
    }
}