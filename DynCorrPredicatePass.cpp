#include "DynCorrPredicatePass.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <chrono>
#include <cstdint>
#include <cstring>
#include <random>
#include <string>

using namespace llvm;

llvm::cl::opt<bool> DynCorrPredicateEnable("obfdyncorr", llvm::cl::init(true), llvm::cl::desc("Dynamic correlated opaque predicate pass."));

static constexpr unsigned PerFunctionCap = 16;
static constexpr unsigned MinBBInsts = 4;
static constexpr unsigned MinSplitGap = 2;
static constexpr const char* DoneMDName = "dyncorr.done";

static std::mt19937_64 Rng;

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasObfuscateAnnotation(Function& f)   { return HasAnnotationTag(f, "obfus"); }
static bool HasNoObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "noobfus"); }
static bool HasNoDynCorrAnnotation(Function& f)   { return HasAnnotationTag(f, "nodyncorr"); }

static bool BBAlreadyProcessed(BasicBlock& bb)
{
    Instruction* term = bb.getTerminator();
    if (!term) return true;
    return term->getMetadata(DoneMDName) != nullptr;
}

static void MarkBBProcessed(BasicBlock& bb)
{
    Instruction* term = bb.getTerminator();
    if (!term) return;
    term->setMetadata(DoneMDName, MDNode::get(bb.getContext(), {}));
}

static bool IsSafeSplitPosition(Instruction& i)
{
    if (isa<PHINode>(&i)) return false;
    if (i.isTerminator()) return false;
    if (isa<AllocaInst>(&i)) return false;
    if (isa<LandingPadInst>(&i)) return false;
    if (isa<CatchPadInst>(&i)) return false;
    if (isa<CleanupPadInst>(&i)) return false;
    if (auto* ii = dyn_cast<IntrinsicInst>(&i))
    {
        auto id = ii->getIntrinsicID();
        if (id == Intrinsic::lifetime_start || id == Intrinsic::lifetime_end) return false;
        if (id == Intrinsic::dbg_declare || id == Intrinsic::dbg_value || id == Intrinsic::dbg_label) return false;
    }
    return true;
}

static bool IsEHOrFuncletInterior(BasicBlock& bb)
{
    if (bb.isEHPad()) return true;
    Instruction* term = bb.getTerminator();
    if (!term) return true;
    if (isa<CatchReturnInst>(term) || isa<CleanupReturnInst>(term) || isa<ResumeInst>(term)) return true;
    for (Instruction& i : bb)
    {
        if (auto* cb = dyn_cast<CallBase>(&i))
        {
            if (cb->countOperandBundlesOfType(LLVMContext::OB_funclet) > 0)
                return true;
        }
    }
    return false;
}

// calls allocas and volatile ops are safe to clone under this pass's P question construction because exactly one arm runs per invocation; only EH pads fences atomic ordering primitives and vaarg must stay single copy
static bool IsSafeToClone(Instruction& i)
{
    if (isa<LandingPadInst>(&i)) return false;
    if (isa<CatchPadInst>(&i)) return false;
    if (isa<CleanupPadInst>(&i)) return false;
    if (isa<FenceInst>(&i)) return false;
    if (isa<AtomicRMWInst>(&i)) return false;
    if (isa<AtomicCmpXchgInst>(&i)) return false;
    if (isa<VAArgInst>(&i)) return false;
    return true;
}

static void CollectSafePositions(BasicBlock& bb, SmallVectorImpl<Instruction*>& out)
{
    out.clear();
    BasicBlock::iterator it = bb.getFirstInsertionPt();
    if (it == bb.end()) return;
    for (; it != bb.end(); ++it)
    {
        if (!IsSafeSplitPosition(*it)) continue;
        out.push_back(&*it);
    }
}

static bool TailContainsUnsafeToClone(BasicBlock& bb, Instruction* posp)
{
    bool reached = false;
    for (Instruction& i : bb)
    {
        if (&i == posp) reached = true;
        if (!reached) continue;
        if (i.isTerminator()) break;
        if (!IsSafeToClone(i)) return true;
    }
    return false;
}

enum class CorrVarForm : unsigned
{
    Alias = 0,
    ArithK = 1,
    LoadTwice = 2,
    Count
};

struct CorrVarResult
{
    Value* PVar = nullptr;
    Value* QVar = nullptr;
    IntegerType* Ty = nullptr;
    CorrVarForm Form = CorrVarForm::Alias;
};

static CorrVarResult HarvestCorrelatedVar(Function& f, BasicBlock& splitbb, DominatorTree& dt, IRBuilder<>& b)
{
    CorrVarResult out;

    const CorrVarForm chosen = (CorrVarForm)(Rng() % (unsigned)CorrVarForm::Count);

    if (chosen == CorrVarForm::LoadTwice)
    {
        SmallVector<AllocaInst*, 8> intallocas;
        for (Instruction& i : f.getEntryBlock())
        {
            if (auto* a = dyn_cast<AllocaInst>(&i))
            {
                if (!a->isStaticAlloca()) continue;
                Type* ty = a->getAllocatedType();
                if (ty->isIntegerTy(32) || ty->isIntegerTy(64))
                    intallocas.push_back(a);
            }
        }
        if (!intallocas.empty())
        {
            AllocaInst* slot = intallocas[(size_t)(Rng() % intallocas.size())];
            IntegerType* ity = cast<IntegerType>(slot->getAllocatedType());
            out.Ty = ity;
            out.Form = CorrVarForm::LoadTwice;
            // two adjacent loads with no intervening store resolve to the same SSA value even after LLVM CSE merges them, preserving the correlation between PVar and QVar
            out.PVar = b.CreateLoad(ity, slot);
            out.QVar = b.CreateLoad(ity, slot);
            return out;
        }
    }

    SmallVector<Value*, 32> cands64, cands32;
    for (Argument& a : f.args())
    {
        if (a.getType()->isIntegerTy(64)) cands64.push_back(&a);
        else if (a.getType()->isIntegerTy(32)) cands32.push_back(&a);
    }
    for (BasicBlock& bb : f)
    {
        if (&bb == &splitbb) continue;
        if (!dt.dominates(&bb, &splitbb)) continue;
        for (Instruction& i : bb)
        {
            if (!i.getType()->isIntegerTy()) continue;
            if (i.getType()->isIntegerTy(64)) cands64.push_back(&i);
            else if (i.getType()->isIntegerTy(32)) cands32.push_back(&i);
        }
    }

    SmallVector<Value*, 32>* pool = nullptr;
    if (!cands64.empty())
    {
        pool = &cands64;
        out.Ty = Type::getInt64Ty(f.getContext());
    }
    else if (!cands32.empty())
    {
        pool = &cands32;
        out.Ty = Type::getInt32Ty(f.getContext());
    }
    else return out;

    Value* v = (*pool)[(size_t)(Rng() % pool->size())];

    if (chosen == CorrVarForm::ArithK)
    {
        // fresh odd none zero k per site breaks inter site CSE across multiple ArithK sites in the same function; both PVar and QVar still equal v+k so the correlation is preserved
        const uint64_t k = ((uint64_t)Rng() | 1ull);
        Value* kconst = ConstantInt::get(out.Ty, k);
        out.Form = CorrVarForm::ArithK;
        out.PVar = b.CreateAdd(v, kconst);
        Value* valias = b.CreateOr(v, ConstantInt::get(out.Ty, 0));
        out.QVar = b.CreateAdd(valias, kconst);
        return out;
    }

    out.Form = CorrVarForm::Alias;
    out.PVar = b.CreateAdd(v, ConstantInt::get(out.Ty, 0));
    out.QVar = b.CreateOr(v, ConstantInt::get(out.Ty, 0));
    return out;
}

enum class PredicateKind : unsigned
{
    Parity = 0,
    BitK = 1,
    Nonzero = 2,
    CmpK = 3,
    Count
};

static Value* EmitPredicate(IRBuilder<>& b, Value* corrvar, IntegerType* ty, PredicateKind kind, bool invertpolarity, uint64_t k)
{
    CmpInst::Predicate pred = invertpolarity ? ICmpInst::ICMP_EQ : ICmpInst::ICMP_NE;

    switch (kind)
    {
        case PredicateKind::Parity:
        {
            Value* lo = b.CreateAnd(corrvar, ConstantInt::get(ty, 1));
            return b.CreateICmp(pred, lo, ConstantInt::get(ty, 0));
        }
        case PredicateKind::BitK:
        {
            const unsigned width = ty->getBitWidth();
            const unsigned bitidx = (unsigned)(k % width);
            const uint64_t mask = (uint64_t)1 << bitidx;
            Value* masked = b.CreateAnd(corrvar, ConstantInt::get(ty, mask));
            return b.CreateICmp(pred, masked, ConstantInt::get(ty, 0));
        }
        case PredicateKind::Nonzero:
        {
            return b.CreateICmp(pred, corrvar, ConstantInt::get(ty, 0));
        }
        case PredicateKind::CmpK:
        {
            return b.CreateICmp(pred, corrvar, ConstantInt::get(ty, k));
        }
        default:
            return ConstantInt::getFalse(b.getContext());
    }
}

static bool TryEmitSite(Function& f, BasicBlock& bb, DominatorTree& dt)
{
    SmallVector<Instruction*, 32> safe;
    CollectSafePositions(bb, safe);
    if (safe.size() < MinBBInsts) return false;

    const unsigned maxidx = (unsigned)safe.size();
    if (maxidx <= MinSplitGap) return false;
    const unsigned pspan = maxidx - MinSplitGap - 1u;
    if (pspan == 0) return false;
    const unsigned pidx = 1u + (unsigned)(Rng() % pspan);
    const unsigned qspan = maxidx - pidx - MinSplitGap;
    if (qspan == 0) return false;
    const unsigned qidx = pidx + MinSplitGap + (unsigned)(Rng() % qspan);
    if (qidx >= maxidx) return false;

    Instruction* posp = safe[pidx];
    Instruction* posq = safe[qidx];

    if (TailContainsUnsafeToClone(bb, posp)) return false;

    // harvest the correlated variable before any split so dominance queries are evaluated against the original BB layout and both aliases dominate posp and everything after
    IRBuilder<> harvestb(posp);
    CorrVarResult cv = HarvestCorrelatedVar(f, bb, dt, harvestb);
    if (!cv.PVar || !cv.QVar) return false;

    const PredicateKind predkind = (PredicateKind)(Rng() % (unsigned)PredicateKind::Count);
    const bool invertpolarity = (Rng() & 1u) != 0u;
    const uint64_t predk = (uint64_t)Rng();

    LLVMContext& c = f.getContext();

    // cloning bb's prefix would double execute it on the cp=false path and corrupt stores counter mutations and SSA chains inside the prefix; clone only [posp..term] so the prefix stays single copy in bb
    BasicBlock* bbheadp = BasicBlock::Create(c, "HeadP", &f);
    ValueToValueMapTy vmap;

    unsigned clonedcount = 0;
    bool startcloning = false;
    for (Instruction& i : bb)
    {
        if (&i == posp) startcloning = true;
        if (!startcloning) continue;
        Instruction* ci = i.clone();
        ci->insertInto(bbheadp, bbheadp->end());
        vmap[&i] = ci;
        ++clonedcount;
    }

    if (clonedcount == 0 || !bbheadp->getTerminator())
    {
        bbheadp->eraseFromParent();
        return false;
    }

    // RF_IgnoreMissingLocals leaves references to the original prefix instructions intact which is correct because bb's prefix dominates bbheadp via the cp=false edge that will be added below
    for (Instruction& ci : *bbheadp)
        RemapInstruction(&ci, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);

    Instruction* posqclone = cast<Instruction>(vmap[posq]);

    BasicBlock* bbtaila = bb.splitBasicBlock(posp, "TailA");
    BasicBlock* bbtailb = bbheadp->splitBasicBlock(posqclone, "TailB");

    // original instructions in bbtaila with uses outside the four BBs become undefined on bbtailb's successor path after the split; SSAUpdater inserts PHIs at the dominance frontier to merge original and clone defs so external uses stay well defined on both paths
    {
        SmallPtrSet<BasicBlock*, 4> ourbbs;
        ourbbs.insert(&bb);
        ourbbs.insert(bbtaila);
        ourbbs.insert(bbheadp);
        ourbbs.insert(bbtailb);

        SmallVector<Instruction*, 16> needrewrite;
        for (Instruction& i : *bbtaila)
        {
            if (i.use_empty()) continue;
            auto vmapit = vmap.find(&i);
            if (vmapit == vmap.end()) continue;
            bool hasexternal = false;
            for (User* u : i.users())
            {
                auto* ui = dyn_cast<Instruction>(u);
                if (!ui) continue;
                if (!ourbbs.contains(ui->getParent()))
                {
                    hasexternal = true;
                    break;
                }
            }
            if (hasexternal) needrewrite.push_back(&i);
        }

        for (Instruction* origi : needrewrite)
        {
            Instruction* clonei = cast<Instruction>(vmap[origi]);

            SSAUpdater updater;
            updater.Initialize(origi->getType(), origi->getName());
            updater.AddAvailableValue(bbtaila, origi);
            updater.AddAvailableValue(clonei->getParent(), clonei);

            SmallVector<Use*, 8> externaluses;
            for (Use& u : origi->uses())
            {
                auto* ui = dyn_cast<Instruction>(u.getUser());
                if (!ui) continue;
                if (ourbbs.contains(ui->getParent())) continue;
                externaluses.push_back(&u);
            }
            for (Use* u : externaluses)
                updater.RewriteUse(*u);
        }
    }

    // bbtailb is a new predecessor of the original successors so every pre existing PHI with an incoming edge from bbtaila needs a parallel incoming edge from bbtailb using the vmap translated value
    for (BasicBlock* succ : successors(bbtailb))
    {
        for (PHINode& phi : succ->phis())
        {
            int idxa = phi.getBasicBlockIndex(bbtaila);
            if (idxa < 0) continue;
            if (phi.getBasicBlockIndex(bbtailb) >= 0) continue;
            Value* valfroma = phi.getIncomingValue((unsigned)idxa);
            Value* valfromb = valfroma;
            if (auto* insta = dyn_cast<Instruction>(valfroma))
            {
                auto it = vmap.find(insta);
                if (it != vmap.end()) valfromb = it->second;
            }
            phi.addIncoming(valfromb, bbtailb);
        }
    }

    // on polarity invert the compare opcode flips NE to EQ so the branch successors are swapped to keep cp=true picking the original path and preserve the correlation invariant between cp and cq
    Instruction* bbterm = bb.getTerminator();
    IRBuilder<> headb(bbterm);
    Value* cp = EmitPredicate(headb, cv.PVar, cv.Ty, predkind, invertpolarity, predk);
    BasicBlock* cptrue = invertpolarity ? bbheadp : bbtaila;
    BasicBlock* cpfalse = invertpolarity ? bbtaila : bbheadp;
    BranchInst* newbr = BranchInst::Create(cptrue, cpfalse, cp);
    ReplaceInstWithInst(bbterm, newbr);

    // cq is built from the original QVar in bb which dominates bbheadp via the cp=false edge; the manual clone deliberately skipped the prefix so there is no cloned qvar to reference
    Instruction* clterm = bbheadp->getTerminator();
    IRBuilder<> headpb(clterm);
    Value* cq = EmitPredicate(headpb, cv.QVar, cv.Ty, predkind, invertpolarity, predk);
    BasicBlock* cqtrue = invertpolarity ? bbtailb : bbtaila;
    BasicBlock* cqfalse = invertpolarity ? bbtaila : bbtailb;
    BranchInst* newbrp = BranchInst::Create(cqtrue, cqfalse, cq);
    ReplaceInstWithInst(clterm, newbrp);

    MarkBBProcessed(bb);
    MarkBBProcessed(*bbheadp);
    MarkBBProcessed(*bbtaila);
    MarkBBProcessed(*bbtailb);

    return true;
}

static BasicBlock* PickNextBB(Function& f)
{
    for (BasicBlock& bb : f)
    {
        if (BBAlreadyProcessed(bb)) continue;
        if (IsEHOrFuncletInterior(bb)) continue;

        SmallVector<Instruction*, 32> safe;
        CollectSafePositions(bb, safe);
        if (safe.size() < MinBBInsts)
        {
            MarkBBProcessed(bb);
            continue;
        }
        return &bb;
    }
    return nullptr;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (HasNoObfuscateAnnotation(f) || HasNoDynCorrAnnotation(f)) return false;
    if (!HasObfuscateAnnotation(f)) return false;

    bool mutated = false;
    for (unsigned i = 0; i < PerFunctionCap; ++i)
    {
        // rebuild DT every iteration because the previous site's splits and PHI inserts invalidate dominance
        DominatorTree dt;
        dt.recalculate(f);

        BasicBlock* bb = PickNextBB(f);
        if (!bb) break;

        if (TryEmitSite(f, *bb, dt))
        {
            mutated = true;
        }
        else
        {
            MarkBBProcessed(*bb);
        }
    }

    return mutated;
}

// strip in pass bookkeeping metadata before returning so intermediate bitcode dumps carry no per BB pass signature
static void StripDoneMetadata(Module& m)
{
    for (Function& f : m)
    {
        for (BasicBlock& bb : f)
        {
            Instruction* term = bb.getTerminator();
            if (!term) continue;
            if (term->getMetadata(DoneMDName))
                term->setMetadata(DoneMDName, nullptr);
        }
    }
}

bool RunDynCorrPredicate(Module& m)
{
    if (!DynCorrPredicateEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x44594E434F525200ULL;
    Rng.seed(seed);

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);

    StripDoneMetadata(m);

    return mutated;
}

PreservedAnalyses DynCorrPredicatePass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunDynCorrPredicate(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}