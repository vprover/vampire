/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file CopyPatchJit.cpp
 * Copy-and-patch JIT compiler for CodeTree matching.
 */

#include "CopyPatchJit.hpp"

#include "Lib/Vector.hpp"
#include "Kernel/FlatTerm.hpp"
#include "Kernel/Term.hpp"

#include <asmjit/core/codeholder.h>
#include <asmjit/x86/x86assembler.h>
#include <asmjit/core.h>

#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <algorithm>
#include <unordered_map>

#ifdef __linux__
  #include <sys/mman.h>
  #include <unistd.h>
#elif defined(_WIN32)
  #include <windows.h>
#elif defined(__APPLE__)
  #include <sys/mman.h>
  #include <unistd.h>
  #include <libkern/OSCacheControl.h>
#endif
//////////////////////////  diagnostics: perf map + JITSTATS counters
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <ostream>

namespace {
inline void perfMapAdd(const void* addr, size_t size, const char* fmt, ...)
{
  static const bool enabled = std::getenv("JIT_PERF_MAP") != nullptr;
  if (!enabled) return;
  static FILE* f = [] {
    char path[64];
    std::snprintf(path, sizeof path, "/tmp/perf-%d.map", (int)getpid());
    return std::fopen(path, "w");
  }();
  if (!f) return;
  char name[128];
  va_list ap; va_start(ap, fmt);
  std::vsnprintf(name, sizeof name, fmt, ap);
  va_end(ap);
  std::fprintf(f, "%zx %zx %s\n", (size_t)addr, size, name);
  std::fflush(f);   // vampire may exit via the instruction-limit path
}
static unsigned long g_emitGen = 0;

//  Marker stored in _altPatchOfs[0] meaning "this op was emitted from the
//  no-alt stencil variant, so it carries NO ALT holes at all, and slot 3 holds
//  its emitted size". Distinct from ALT_PATCH_NONE (0xFFFF) and from every real
//  hole offset (all < 256, the stencils top out at 246 bytes).
static constexpr uint16_t ALT_NOALT_TAG = 0xFFFE;


// Distance from the start of a jmpAlt site (the movabs opcode) to the return
// address pushed by the site's 'call [rbp+bindJmpAltStub]'. All jmpAlt sites
// share one byte-identical layout, so this is measured once during stencil
// compilation (emitJmpAlt) and asserted equal on every subsequent emission.
static size_t s_jmpAltRetOfs = 0;

struct JitStats {
  size_t emitBlocks = 0, emitBytes = 0, emitOps = 0;
  size_t ssEmits = 0, ssBytes = 0;
  size_t ssLookups = 0, ssFound = 0;
  size_t ssDirectStubs = 0;    // landing stubs using the direct jmp rel32 form
  size_t ssIndirectStubs = 0;  // landing stubs left on jmp [rbp + ssDispatchStub]
  size_t frees = 0;
  size_t patchAltCalls = 0, patchAltStores = 0;
  size_t lazyCompiles = 0;
  size_t slabsMapped = 0, slabBytes = 0;
  size_t jitInstances = 0;     // CodeTrees that JIT-compiled in this run (1 on UEQ, 2 on FOF)

  //  tiered compilation
  size_t tierDeopts = 0;       // entries into a block too cold to compile
  size_t tierCompiled = 0;     // blocks that reached the threshold and were emitted
  size_t deoptViaLazy = 0;     // deopts resolved through lazyCompileHelper
  size_t deoptViaBind = 0;     // deopts resolved through bindJmpAltHelper (site left unbound)
                               //   invariant: deoptViaLazy + deoptViaBind == tierDeopts
  size_t reemitQueued = 0;     // blocks queued for re-emission on a late alternative
  size_t reemitBlocks = 0;     // blocks actually re-emitted
  size_t reemitOps = 0;        // OPS re-emitted by the queue (not bytes)
  size_t reemitTooBig = 0;     // late alternatives on blocks over the op cap
  size_t reemitFallback = 0;   // late alternatives that fell back to the out-of-line patch
  size_t reemitNoReferrer = 0; // re-emitted blocks with no recorded referrer (entry point, or a gap)
  size_t entryNotHead = 0;     // literal entries skipped by the eager compile because the
                               //   entry op is mid-block (ClauseCodeTree enters at litEndOp+1);
                               //   those literals run interpreted ie expected non-zero on clause trees
  size_t backptrPeak = 0;      // largest live entry count any ONE tree reached
  size_t backptrRemoves = 0;   // keys dropped; should track frees, cf unbinds
  size_t backptrChecks = 0;    // removals that cross-checked map against scan
  size_t backptrMismatch = 0;  // TRIPWIRE: map disagreed with the scan. Must be 0.
  size_t backptrSets = 0;      // setReferrer calls, re-points included
  size_t treeEmpty = 0;    

  // PLT-style binding of jmpAlt sites
  size_t bindCalls = 0;        // trips through the bind stub (once per site per bind epoch)
  size_t binds = 0;            // sites patched to direct 'jmp rel32'
  size_t unbinds = 0;          // bound sites restored to initial form by patchAlternative
  size_t bindUnreachable = 0;  // target outside +-2 GB: left unbound (fallback slabs only)

  size_t execRegionMB = 0;     // size of the reserved exec region actually obtained
  size_t budgetStops = 0;      // times the soft code budget refused a JIT entry
  size_t budgetStopsLive = 0;  // of those, the ones holding live JIT backtrack
                               // entries that had to be migrated

  //  Tripwires - all should stay 0 in a healthy run
  size_t deoptNullOp = 0;      // deopt with ctx->op unset: interpreter resumes at a stale op
  size_t bindBadSite = 0;      // site head bytes unexpected: refused to patch
  size_t patchBadSite = 0;     // patchAlternative met unexpected head bytes: refused
  size_t budgetBailouts = 0;   //HARD budget aborted a match mid-flight

  // trampoline instrumentation
  size_t btPops = 0;           // backtrack-stack pops resumed by the bt handler
  size_t opsExec = 0;          // entries into a compiled op. JIT_RATE_COUNTERS only.
  size_t blockOps = 0;         // sum of block lengths over block-HEAD entries.
                               //   The cheap stand-in for opsExec: 11 bytes per
                               //   block instead of 13 per op. JIT_RATE_COUNTERS
                               //   only. See emitBlockHeadCounter.
                               //   The ONLY counter that measures how much
                               //   COMPILED code runs: everything else is image
                               //   size or uncompiled-path traffic (deopts,
                               //   lazy compiles, binds)

  size_t emitOpsByKind[7] = {0};
  size_t emitBytesByKind[7] = {0};
  size_t altNull = 0, altNonNull = 0;
  size_t altFirstAppear = 0;   // ops emitted null that later got an alternative
  size_t oolPatches = 0;       // out-of-line op copies installed
  size_t oolBytes = 0;         // bytes in those copies (NOT counted in emitBytes)
  size_t oolUnreachable = 0;   // copy or successor outside +-2 GB: UNSOUND (must stay 0)
  size_t oolFailed = 0;        // could not emit the copy: UNSOUND (must stay 0)
  size_t altLostPatch = 0;     // late alternative with nowhere to go: UNSOUND (must stay 0)
  size_t ssLenHist[7] = {0};
};

JitStats g_jitStats;

//  Process-wide executable-memory state.
//
//  Previously these were members of CopyPatchJit, and every CodeTree owns one
//  - so each index reserved its own region and carried its own budget. Two
//  live trees therefore charged 2 x EXEC_REGION_SIZE of virtual address space
//  (Vampire's -m check measures virtual size, so that is charged as if it
//  were consumed) and allowed 2 x the intended code budget. Both quantities
//  belong to the process, so they live here.
//
//  Not thread-safe. Vampire's portfolio mode forks; if it ever threads the
//  prover, these need a mutex.
char*  g_execRegionBase   = nullptr;
size_t g_execRegionSize   = 0;
size_t g_execRegionUsed   = 0;
bool   g_execRegionFailed = false;

//  NOTE: the budget counters themselves are NOT here - they need external
//  linkage so the inline predicates in the header can see them. See
//  Indexing::JitBudget below.

//  Slabs released by a destroyed CodeTree, available for reuse. Without this
//  the region's bump pointer would never rewind and a run that creates and
//  destroys many trees would exhaust it.
struct FreeSlabRec { void* base; size_t capacity; };
std::vector<FreeSlabRec> g_freeSlabs;
}

static_assert(sizeof(Kernel::TermList) == 8, "JIT assumes sizeof(TermList) == 8");
static_assert(sizeof(Kernel::FlatTerm::Entry) == 8, "JIT assumes sizeof(FlatTerm::Entry) == 8");

// Layout assumptions used by the trampoline's literal iteration code.
// FlatTerm: { size_t _length; Entry _data[1]; } -> _data at offset 8.
// LitInfo:  { unsigned liIndex; unsigned litIndex; FlatTerm* ft; bool opposite; }
static_assert(sizeof(Indexing::CodeTree::LitInfo) == 24,
    "JIT literal iteration assumes sizeof(LitInfo) == 24");
static_assert(offsetof(Indexing::CodeTree::LitInfo, ft) == 8,
    "JIT literal iteration assumes LitInfo::ft at offset 8");


namespace Indexing {

using namespace asmjit;
using namespace asmjit::x86;

//  Process-wide code budget (declared in CopyPatchJit.hpp). Starts at the
//  default so the inline predicates never have to test for "unset"; the
//  CodeTree constructor lowers it once the -m limit is known.
namespace JitBudget {
  size_t emittedTotal = 0;
  size_t codeBudget   = CopyPatchJit::CODE_BUDGET_DEFAULT;
}

//  True base address of every compiled block's allocation, keyed on its first
//  op.
//
//  Needed because CodeOp::_mcode is NOT reliably the block's base: the
//  out-of-line patch path in patchAlternative ends with op->_mcode = copy,
//  repointing a block HEAD at a standalone out-of-line copy. Anything that
//  frees or relocates a block must consult this map rather than _mcode.
//  Erased by forgetBlockBase, which freeJitBlock calls.
static std::unordered_map<const void*, void*> g_blockBase;

//  JIT_REEMIT=1 replaces the out-of-line patch of the no-alt variant with
//  whole-block re-emission.
//
//  An op emitted from the no-alt variant that later acquires an alternative
//  currently gets a 158-to-182-byte out-of-line trampoline hung off its head.
//
//  Re-emitting the one block gets that win without the bulk pass's +1.97%
//  instruction bill.
static bool reemitEnabled()
{
  static const bool on = [] {
    const char* s = std::getenv("JIT_REEMIT");
    return s ? (strtoll(s, nullptr, 10) != 0) : true;
  }();
  return on;
}

//  Largest block worth re-emitting, in ops. JIT_REEMIT_MAX_OPS overrides.
//
//  Re-emission costs O(ops in the block) and buys O(patches in that block), so
//  the ratio degrades linearly with block size.
//
//  Applied per block, so a large-block problem still re-emits whichever of its
//  blocks are small and falls back to the out-of-line patch only on the rest.
static size_t reemitMaxOps()
{
  static const size_t kDefault = 64;
  static const size_t n = [] {
    const char* s = std::getenv("JIT_REEMIT_MAX_OPS");
    return s ? strtoull(s, nullptr, 10) : kDefault;
  }();
  return n;
}

void CopyPatchJit::printJitStats(std::ostream& out)
{
  const JitStats& s = g_jitStats;
  if (!s.emitBlocks && !s.ssEmits && !s.slabsMapped) return;
  out << "% JITSTATS"
      << " emit_blocks=" << s.emitBlocks
      << " emit_bytes=" << s.emitBytes
      << " emit_ops=" << s.emitOps
      << " ss_emits=" << s.ssEmits
      << " ss_bytes=" << s.ssBytes
      << " ss_lookups=" << s.ssLookups
      << " ss_found=" << s.ssFound
      << " tier_deopts=" << s.tierDeopts
      << " tier_compiled=" << s.tierCompiled
      << " entry_not_head=" << s.entryNotHead
      << " backptr_peak=" << s.backptrPeak
      << " backptr_removes=" << s.backptrRemoves
      << " backptr_checks=" << s.backptrChecks
      << " backptr_mismatch=" << s.backptrMismatch
      << " backptr_sets=" << s.backptrSets
      << " tree_empty=" << s.treeEmpty
      << " jit_instances=" << s.jitInstances
      << " deopt_nullop=" << s.deoptNullOp
      << " deopt_via_lazy=" << s.deoptViaLazy
      << " deopt_via_bind=" << s.deoptViaBind
      << " frees=" << s.frees
      << " patch_alt_calls=" << s.patchAltCalls
      << " patch_alt_stores=" << s.patchAltStores
      << " lazy_compiles=" << s.lazyCompiles
      << " slabs=" << s.slabsMapped
      << " slab_bytes=" << s.slabBytes
      //  Which THP arm ran. Verifies the intent only (that the kernel actually
      //  backed the region with 2 MiB pages is AnonHugePages in smaps)
      << " thp=" << (std::getenv("JIT_NO_THP") ? 0 : 1)
      << " bind_calls=" << s.bindCalls
      << " binds=" << s.binds
      << " unbinds=" << s.unbinds
      << " bind_unreachable=" << s.bindUnreachable
      << " bind_badsite=" << s.bindBadSite
      << " patch_badsite=" << s.patchBadSite
      << " exec_region_mb=" << s.execRegionMB
      << " code_budget_mb=" << (CopyPatchJit::codeBudget() >> 20)
      << " emitted_total_mb=" << (CopyPatchJit::emittedTotal() >> 20)
      << " budget_stops=" << s.budgetStops
      << " budget_stops_live=" << s.budgetStopsLive
      << " budget_bailouts=" << s.budgetBailouts
      << " bt_pops=" << s.btPops
      << " ops_exec=" << s.opsExec
      << " block_ops=" << s.blockOps
      << " reemit_queued=" << s.reemitQueued
      << " reemit_blocks=" << s.reemitBlocks
      << " reemit_ops=" << s.reemitOps
      << " reemit_toobig=" << s.reemitTooBig
      << " reemit_fallback=" << s.reemitFallback
      << " reemit_noreferrer=" << s.reemitNoReferrer;

  {
    static const char* kindName[7] = {"sof","cgt","lend","cfun","avar","cvar","ss"};
    for (unsigned i = 0; i < 7; i++) {
      if (!s.emitOpsByKind[i]) continue;
      out << " ops_" << kindName[i] << "=" << s.emitOpsByKind[i]
          << " bytes_" << kindName[i] << "=" << s.emitBytesByKind[i];
    }
  }
  out << " alt_null=" << s.altNull << " alt_nonnull=" << s.altNonNull
      << " alt_first_appear=" << s.altFirstAppear
      << " ool_patches=" << s.oolPatches
      << " ool_bytes=" << s.oolBytes
      << " ool_unreachable=" << s.oolUnreachable
      << " ool_failed=" << s.oolFailed
      << " alt_lost_patch=" << s.altLostPatch;

  out << " ss_direct_stubs=" << s.ssDirectStubs
      << " ss_indirect_stubs=" << s.ssIndirectStubs;
  out << " ss_len_hist=";
  for (unsigned i = 0; i < 7; i++) out << (i ? "," : "") << s.ssLenHist[i];

  out << std::endl;
}

//  Block-base bookkeeping. See g_blockBase for why _mcode will not do.
void* CopyPatchJit::blockBase(const void* firstOp)
{
  auto it = g_blockBase.find(firstOp);
  return it == g_blockBase.end() ? nullptr : it->second;
}

void CopyPatchJit::forgetBlockBase(const void* firstOp)
{
  g_blockBase.erase(firstOp);
}

bool CopyPatchJit::reemitOn() { return reemitEnabled(); }

//  Is this op in the no-alt tagged form, i.e. emitted with no ALT hole at all?
bool CopyPatchJit::isNoAltTagged(const CodeTree::CodeOp* op)
{
  return op->_altPatchOfs[0] == ALT_NOALT_TAG;
}

//  The op's index within its block, stashed in slot 1 at emission.
//
//  Slots 0 and 3 carry the tag and the emitted size; 1 and 2 are unused in the
//  tagged form, which is the only form this is asked about. Returns
//  ALT_PATCH_NONE when the index did not fit, in which case the caller must
//  fall back to the out-of-line patch.
unsigned CopyPatchJit::noAltOpIndex(const CodeTree::CodeOp* op)
{
  return op->_altPatchOfs[1];
}

unsigned CopyPatchJit::altIndexUnknown() { return CodeTree::CodeOp::ALT_PATCH_NONE; }

size_t CopyPatchJit::reemitBlockOpCap() { return reemitMaxOps(); }
void   CopyPatchJit::noteReemitTooBig() { g_jitStats.reemitTooBig++; }

void CopyPatchJit::noteReemitQueued()      { g_jitStats.reemitQueued++; }
void CopyPatchJit::noteReemitFallback()    { g_jitStats.reemitFallback++; }
void CopyPatchJit::noteReemitNoReferrer()  { g_jitStats.reemitNoReferrer++; }
void CopyPatchJit::noteReemitBlock(size_t nOps)
{ g_jitStats.reemitBlocks++; g_jitStats.reemitOps += nOps; }

void CopyPatchJit::recordBtPops(size_t n)
{
  #if defined(JIT_RATE_COUNTERS) || defined(JIT_GATE_COUNTERS)
  g_jitStats.btPops += n;
  #else
    (void)n;
  #endif
}

void CopyPatchJit::recordBlockOps(size_t n)
{
  #if defined(JIT_RATE_COUNTERS) || defined(JIT_GATE_COUNTERS)
  g_jitStats.blockOps += n;
  #else
    (void)n;
  #endif
}

void CopyPatchJit::recordBudgetStop()
{
  g_jitStats.budgetStops++;
}

void CopyPatchJit::recordBudgetStopLive()
{
  g_jitStats.budgetStopsLive++;
}

//  The soft-budget backtrack migration. Default ON.
static bool budgetFixEnabled()
{
  static const bool on = [] {
    const char* s = std::getenv("JIT_BUDGET_FIX");
    return s ? (strtoll(s, nullptr, 10) != 0) : true;
  }();
  return on;
}

bool CopyPatchJit::budgetFixOn() { return budgetFixEnabled(); }

/*
 * Tiering: how many times a block has been entered, keyed on its first op.
 *
 * Erased by forgetBlockEntries when a block is freed, which freeJitBlock calls
 * unconditionally. Leaving an entry behind is NOT harmless: CodeBlocks are heap
 * allocations and addresses get reused, so a fresh block inheriting a dead
 * one's count crosses JIT_TIER_THRESHOLD early and is compiled before it has
 * earned it. That produced five different emit_blocks readings for the same
 * problem before the erase was added (cost analysis 28).
 */
static std::unordered_map<const void*, unsigned> g_blockEntries;

unsigned CopyPatchJit::noteBlockEntry(const void* firstOp)
{ return ++g_blockEntries[firstOp]; }

//  Erase a freed block's tier count.
//
//  Without this, the entry survives the block and a later CodeBlock allocated
//  at the same heap address inherits it, crossing JIT_TIER_THRESHOLD early.
//  Erasing is also the semantically correct choice: a freshly allocated block
//  should earn its own compilation, not inherit a dead block's credit.
void CopyPatchJit::forgetBlockEntries(const void* firstOp)
{
  g_blockEntries.erase(firstOp);
}


bool CopyPatchJit::deoptAllowed()
{
  static const size_t limit = [] {
    const char* s = std::getenv("JIT_DEOPT_LIMIT");
    return s ? strtoull(s, nullptr, 10) : ~size_t(0);
  }();
  static size_t seen = 0;
  return ++seen <= limit;
}

//  The two helpers below are static (they are called from emitted code), so
//  they cannot reach _deoptStub through an instance. There is one exec-code
//  region per process, hence one deopt stub; cache its address here when it is
//  compiled.
void* CopyPatchJit::_deoptStubAddr = nullptr;

void CopyPatchJit::recordTierDeopt()   { g_jitStats.tierDeopts++; }
void CopyPatchJit::recordEntryNotHead()   { g_jitStats.entryNotHead++; }
void CopyPatchJit::recordBackptrPeak(size_t liveEntries)
{ if (liveEntries > g_jitStats.backptrPeak) g_jitStats.backptrPeak = liveEntries; }
void CopyPatchJit::recordBackptrRemove()   { g_jitStats.backptrRemoves++; }
void CopyPatchJit::recordBackptrCheck()    { g_jitStats.backptrChecks++; }
void CopyPatchJit::recordBackptrMismatch() { g_jitStats.backptrMismatch++; }
void CopyPatchJit::recordBackptrSet() { g_jitStats.backptrSets++; }
void CopyPatchJit::recordEmptyTree()  { g_jitStats.treeEmpty++; }
void CopyPatchJit::recordDeoptNullOp()       { g_jitStats.deoptNullOp++; }
void CopyPatchJit::recordTierCompile() { g_jitStats.tierCompiled++; }

void CopyPatchJit::setCodeBudget(size_t bytes)
{
  //  Every CodeTree constructor calls this with the same value derived from
  //  -m; taking the smallest is the safe tie-break if they ever disagree, and
  //  never raising it keeps the cap a property of the process rather than of
  //  whichever index happened to be built last.
  size_t b = bytes ? bytes : CODE_BUDGET_DEFAULT;

  //  JIT_BUDGET_LIMIT=<bytes> lowers the soft budget far enough that the
  //  crossing is reachable on a gate problem in seconds, exactly as
  //  JIT_DEOPT_LIMIT made the deopt paths reachable
  static const size_t envLimit = [] {
    const char* s = std::getenv("JIT_BUDGET_LIMIT");
    return s ? strtoull(s, nullptr, 10) : size_t(0);
  }();
  if (envLimit && envLimit < b) { b = envLimit; }

  if (b < JitBudget::codeBudget) { JitBudget::codeBudget = b; }
}

const char* CopyPatchJit::jitModeName() {
  switch (JIT_MODE) {
    case JitMode::Off:        return "off";
    case JitMode::ClauseOnly: return "clause";
    case JitMode::TermOnly:   return "term";
    case JitMode::Both:       return "both";
  }
  return "?";
}

//  expand the backtrack buffer when full
void CopyPatchJit::expandBtBufferHelper(JitExecContext* ctx) {
  auto base   = static_cast<char*>(ctx->btBase);
  auto cursor = static_cast<char*>(ctx->btCursor);
  auto end    = static_cast<char*>(ctx->btEnd);
  size_t used    = static_cast<size_t>(cursor - base);
  size_t oldSize = static_cast<size_t>(end - base);
  size_t newSize = oldSize * 2;
  auto newBuf = static_cast<char*>(realloc(base, newSize));
  ctx->btBase   = newBuf;
  ctx->btCursor = newBuf + used;
  ctx->btEnd    = newBuf + newSize;
}

void CopyPatchJit::expandEntryHelper(FlatTerm::Entry* entry) {
  entry->expand();
}

void* CopyPatchJit::lazyCompileHelper(JitExecContext* ctx, CodeTree::CodeOp* alt) {
  if (!alt) return nullptr;
  auto* tree = static_cast<CodeTree*>(ctx->codeTree);
  // HARD budget only: the soft limit is enforced at executeMachineCode entry,
  // so an in-flight match is allowed to finish compiling what it needs. If we
  // are past even the hard limit, refuse and signal C++ to abort the match -
  // returning nullptr alone would look like "no alternative" to the caller and
  // silently drop a branch.
  if (budgetExhausted()) {
    g_jitStats.budgetBailouts++;
    ctx->bailout = 1;
    return nullptr;
  }
  g_jitStats.lazyCompiles++;
  void* res = tree->lazyCompileBlock(alt);
  //  Compare against THIS tree's stub, not the static _deoptStubAddr: every
  //  CodeTree owns a CopyPatchJit and each compiles its own deopt stub, so the
  //  static names only the last one to initialize. lazyCompileBlock returns
  //  tree->_cpJit->deoptStub(), so with two live trees the old test silently
  //  failed and ctx->op was never set.
  if (res == tree->_cpJit->deoptStub()) {
    //  The block was too cold to compile, so the caller is about to jump into
    //  the deopt stub. That stub saves the register file but cannot know which
    //  op the interpreter should resume at, only we do.
    g_jitStats.deoptViaLazy++;
    ctx->op = alt;
  }
  return res;
}

/*
 * bindJmpAltHelper - the resolver behind PLT-style lazy binding of jmpAlt
 * dispatch sites.
 *
 * A jmpAlt site has two states:
 *
 *   initial:  movabs rax, <CodeOp*> ; test ; jz .bt ; call [rbp+bindJmpAltStub]
 *   bound:    jmp rel32 <target mcode>   (overwrites the first 5 movabs bytes;
 *             bytes +5..+9 become dead, the rest of the site is unreachable
 *             but intact so patchAlternative can restore the initial form)
 */
void* CopyPatchJit::bindJmpAltHelper(JitExecContext* ctx, CodeTree::CodeOp* alt, void* retAddr)
{
  g_jitStats.bindCalls++;
  if (!alt) return nullptr;
  auto* tree = static_cast<CodeTree*>(ctx->codeTree);
  if (budgetExhausted()) {                 // see lazyCompileHelper
    g_jitStats.budgetBailouts++;
    ctx->bailout = 1;
    return nullptr;
  }
  void* target = alt->_mcode;
  if (!target) {
    g_jitStats.lazyCompiles++;
    target = tree->lazyCompileBlock(alt);
  }
  if (!target) return nullptr;
  if (target == tree->_cpJit->deoptStub()) {   // this tree's stub - see lazyCompileHelper
    //  Cold block: hand this dispatch to the interpreter, and do NOT bind the
    //  site. Binding would wire a jmp rel32 straight to the deopt stub, so
    //  this site would never consult the counter again and the block could
    //  never become hot - the whole tiering mechanism would be dead for every
    //  bound edge.
    g_jitStats.deoptViaBind++;
    ctx->op = alt;
    return target;
  }
  // SearchStruct alternatives are bindable too: the 16-byte landing stub is
  // emitted once and freed only when the SS is destroyed, and every
  // destruction path repoints + patchAlternatives the (single) incoming op
  // before JIT code runs again

  uint8_t* siteHead = static_cast<uint8_t*>(retAddr) - s_jmpAltRetOfs;
  // Defensive: only patch if the site head is the movabs we emitted.
  if (siteHead[0] != 0x48 || siteHead[1] != 0xB8) {
    g_jitStats.bindBadSite++;
    return target;
  }
  intptr_t rel = static_cast<char*>(target) - reinterpret_cast<char*>(siteHead + 5);
  if (rel < static_cast<intptr_t>(INT32_MIN) || rel > static_cast<intptr_t>(INT32_MAX)) {
    g_jitStats.bindUnreachable++;
    return target;
  }
  uint8_t patch[5];
  patch[0] = 0xE9;
  int32_t r32 = static_cast<int32_t>(rel);
  memcpy(patch + 1, &r32, 4);
  memcpy(siteHead, patch, 5);   // single-threaded; x86 I/D caches are coherent
  g_jitStats.binds++;
  return target;
}

/*
 * ssLookupHelper - the data side of data-driven SearchStructs.
 * The shared dispatch stub passes the live register-file ftData/tp as
 * arguments (ctx copies are stale during JIT execution). getTargetOp is the
 * same routine the interpreter uses: isFun check, then binary search over the
 * mutable values[] vector. A wrong-slot result is harmless - targets are
 * CHECK ops that re-verify the functor/term themselves and route to
 * backtrack on mismatch, exactly as in the interpreter.
 */
CodeTree::CodeOp* CopyPatchJit::ssLookupHelper(JitExecContext* /*ctx*/, CodeTree::CodeOp* landingOp,
                                               FlatTerm::Entry* ftData, size_t tp)
{
  CodeTree::SearchStruct* ss = landingOp->getSearchStruct();
  #ifdef JIT_RATE_COUNTERS
    {
      size_t len = ss->length();
      unsigned b = len <= 2 ? 0 : len <= 4 ? 1 : len <= 8 ? 2
                : len <= 16 ? 3 : len <= 32 ? 4 : len <= 64 ? 5 : 6;
      g_jitStats.ssLenHist[b]++;
    }
  #endif
#ifdef JIT_RATE_COUNTERS
  g_jitStats.ssLookups++;
#endif
  CodeTree::CodeOp* target = ss->getTargetOp(ftData + tp);
#ifdef JIT_RATE_COUNTERS
  if (target) g_jitStats.ssFound++;
#endif
  return target;
}

//  bit patterns used as immediates in stencil compilation.  After compiling a stencil with asmjit, we scan
//  for these patterns to locate the holes that need patching at emission.
//
//  Every placeholder is chosen so that:
//    (a) it won't appear in normal instruction encodings, and
//    (b) 8-byte placeholders are forced via raw 'embed()' to avoid
//        asmjit optimizing 'mov rax,0' -> 'xor eax,eax'

static constexpr uint64_t PH_ALT1     = 0xAA00'0000'0000'0001ULL;
static constexpr uint64_t PH_ALT2     = 0xAA00'0000'0000'0002ULL;
static constexpr uint32_t PH_FUNC     = 0xBB00'0001U;
static constexpr uint32_t PH_VAROFS   = 0xDD00'0001U;
static constexpr uint64_t PH_GTERM    = 0xEE00'0000'0000'0001ULL;
static constexpr uint64_t PH_OPPTR    = 0xFF00'0000'0000'0001ULL;
// For the jmp-to-next-stencil, we use a raw rel32 placeholder:
static constexpr int32_t  PH_NEXT32   = 0x7766'5544;
static constexpr uint32_t PH_BLOCKLEN = 0xCC00'0001U;

//  Helper: emit 'movabs rax, imm64' as 10 raw bytes (REX.W + B8 + imm)
//  Prevents asmjit from optimizing zero values to 'xor eax,eax'
static size_t emitMovAbsRax(Assembler& a, uint64_t val) {
  size_t immOfs = a.offset() + 2;   // +2 skips REX.W(0x48) + opcode(0xB8)
  uint8_t buf[10] = { 0x48, 0xB8 };
  memcpy(buf + 2, &val, 8);
  a.embed(buf, 10);
  return immOfs;
}

static size_t emitMovAbsRcx(Assembler& a, uint64_t val) {
  size_t immOfs = a.offset() + 2;   // +2 skips REX.W(0x48) + opcode(0xB9)
  uint8_t buf[10] = { 0x48, 0xB9 };
  memcpy(buf + 2, &val, 8);
  a.embed(buf, 10);
  return immOfs;
}

static size_t emitMovAbsRdx(Assembler& a, uint64_t val) {
  size_t immOfs = a.offset() + 2;   // +2 skips REX.W(0x48) + opcode(0xBA)
  uint8_t buf[10] = { 0x48, 0xBA };
  memcpy(buf + 2, &val, 8);
  a.embed(buf, 10);
  return immOfs;
}

/*
 * count every entry into a compiled op. 13 bytes, and ONLY under JIT_RATE_COUNTERS.
/*
 * emitBlockHeadCounter - one add per BLOCK ENTRY, weighted by the block's own
 * length, accumulating the quantity cost analysis 40's model needs without
 * paying emitOpsExecInc's 13 bytes on every op.
 *
 *   add qword ptr [rbp + blockOps], <block length>
 *   48 81 85 <disp32> <imm32>     -> 11 bytes
 */
static void emitBlockHeadCounter(Assembler& a, Stencil& s, size_t base)
{
#if defined(JIT_RATE_COUNTERS) || defined(JIT_GATE_COUNTERS)
  size_t ofs = a.offset() - base;
  uint8_t buf[11] = { 0x48, 0x81, 0x85 };   // REX.W ADD r/m64, imm32; [rbp+disp32]
  uint32_t disp = static_cast<uint32_t>(offsetof(JitExecContext, blockOps));
  memcpy(buf + 3, &disp, 4);
  memcpy(buf + 7, &PH_BLOCKLEN, 4);
  a.embed(buf, 11);
  //  The hole is the 4-byte immediate, 7 bytes into the instruction.
  s.holes.push_back({StencilHole::BLOCK_LEN_IMM32,
                     static_cast<uint16_t>(ofs + 7)});
#else
  (void)a; (void)s; (void)base;
#endif
}

static void emitOpsExecInc(Assembler& a)
{
#ifdef JIT_RATE_COUNTERS
  emitMovAbsRax(a, reinterpret_cast<uint64_t>(&g_jitStats.opsExec));
  a.inc(qword_ptr(rax));
#else
  (void)a;
#endif
}



//  Shared JitRuntime
static JitRuntime& sharedRuntime() {
  static JitRuntime rt;
  return rt;
}

//  Extract raw machine code bytes from a CodeHolder. All internal relative jumps are already resolved by the Assembler
static std::vector<uint8_t> extractCode(CodeHolder& code) {
  void* ptr = nullptr;
  Error err = sharedRuntime().add(&ptr, &code);
  (void)err;
  ASS(err == Error::kOk && "asmjit add() failed during stencil extraction");
  size_t sz = code.code_size();
  std::vector<uint8_t> buf(sz);
  memcpy(buf.data(), ptr, sz);
  sharedRuntime().release(ptr);
  return buf;
}


//  Executable memory management
//
//  Fallback path only: slabs are normally carved from the reserved exec
//  region (see ensureExecRegion). This is used when the region could not be
//  mapped or is exhausted; sites binding across mappings then rely on the
//  rel32 reachability guard in bindJmpAltHelper.

#ifdef __linux__
static int execThpAdvice()
{
  static const int advice =
      std::getenv("JIT_NO_THP") ? MADV_NOHUGEPAGE : MADV_HUGEPAGE;
  return advice;
}
#endif

static void* mapExecPages(size_t size) {
#ifdef __linux__
  const size_t TWO_MB = size_t(2) << 20;
  ASS((size & (TWO_MB - 1)) == 0);
  size_t over = size + TWO_MB;
  char* p = (char*)mmap(nullptr, over, PROT_READ | PROT_WRITE | PROT_EXEC,
                        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) return nullptr;
  char* aligned = (char*)(((uintptr_t)p + TWO_MB - 1) & ~(uintptr_t)(TWO_MB - 1));
  ASS(((uintptr_t)aligned & (TWO_MB - 1)) == 0);
  if (size_t head = size_t(aligned - p)) munmap(p, head);
  if (size_t tail = over - size_t(aligned - p) - size) munmap(aligned + size, tail);
  madvise(aligned, size, execThpAdvice());
  return aligned;
#elif defined(__APPLE__)
  void* p = mmap(nullptr, size, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
  return (p == MAP_FAILED) ? nullptr : p;
#elif defined(_WIN32)
  return VirtualAlloc(nullptr, size, MEM_COMMIT | MEM_RESERVE,
                      PAGE_EXECUTE_READWRITE);
#else
  // Fallback
  return aligned_alloc(4096, (size + 4095) & ~4095UL);
#endif
}

static void unmapExecPages(void* ptr, size_t size) {
#ifdef __linux__
  munmap(ptr, size);
#elif defined(__APPLE__)
  munmap(ptr, size);
#elif defined(_WIN32)
  VirtualFree(ptr, 0, MEM_RELEASE);
#else
  free(ptr);
#endif
}

// flush icache on architectures that need it. x86-64 has coherent I/D caches, so this is a no-op
static inline void flushICache(void* /*addr*/, size_t /*size*/) {
#if defined(__APPLE__) && defined(__aarch64__)
  sys_icache_invalidate(addr, size);
#endif
}

/*
 * Reserve one large RWX mapping up front (Linux). All slabs are carved from
 * it by bumping, which guarantees any two code addresses are within +-2 GB of
 * each other - the precondition for binding jmpAlt sites to direct
 * 'jmp rel32'. MAP_NORESERVE + never touching unused pages keeps the cost of
 * the reservation at zero. 2 MB-aligned so carved slabs are THP-eligible.
 * On failure the size is halved down to 256 MB before giving up; without a
 * region everything still works via per-slab mappings, just with fewer sites
 * bindable (bind_unreachable counts them).
 */
void CopyPatchJit::ensureExecRegion() {
  if (g_execRegionBase || g_execRegionFailed) return;
#ifndef __linux__
  g_execRegionFailed = true;
  return;
#else
  const size_t TWO_MB = size_t(2) << 20;
  size_t want = EXEC_REGION_SIZE;
  while (want >= (size_t(256) << 20)) {
    size_t over = want + TWO_MB;
    char* p = (char*)mmap(nullptr, over, PROT_READ | PROT_WRITE | PROT_EXEC,
                          MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (p != MAP_FAILED) {
      char* aligned = (char*)(((uintptr_t)p + TWO_MB - 1) & ~(uintptr_t)(TWO_MB - 1));
      if (size_t head = size_t(aligned - p)) munmap(p, head);
      if (size_t tail = over - size_t(aligned - p) - want) munmap(aligned + want, tail);
      g_execRegionBase = aligned;
      g_execRegionSize = want;
      g_execRegionUsed = 0;
      g_jitStats.execRegionMB = want >> 20;
      return;
    }
    want >>= 1;
  }
  g_execRegionFailed = true;
#endif
}

void CopyPatchJit::ensureSlabSpace(size_t size) {
  if (!_slabs.empty() && _slabs.back().used + size <= _slabs.back().capacity) return;

  const size_t TWO_MB = size_t(2) << 20;
  size_t cap = std::max(SLAB_SIZE, size);
  cap = (cap + TWO_MB - 1) & ~(TWO_MB - 1);   // THP: whole 2 MiB units

  //  Prefer a slab released by a previously destroyed tree over new space.
  for (size_t i = 0; i < g_freeSlabs.size(); i++) {
    if (g_freeSlabs[i].capacity >= cap) {
      ExecSlab s{g_freeSlabs[i].base, g_freeSlabs[i].capacity, 0, 0, true};
      g_freeSlabs[i] = g_freeSlabs.back();
      g_freeSlabs.pop_back();
      _slabs.push_back(s);
      return;   // already counted in slabsMapped/slabBytes when first mapped
    }
  }

  ensureExecRegion();
  void* p = nullptr;
  bool inRegion = false;
  if (g_execRegionBase && g_execRegionUsed + cap <= g_execRegionSize) {
    p = g_execRegionBase + g_execRegionUsed;
    g_execRegionUsed += cap;
    inRegion = true;
#ifdef __linux__
    madvise(p, cap, execThpAdvice());
#endif
  } else {
    //  Region exhausted (or unavailable): fall back to an individual mapping.
    //  Correct, but it does add virtual footprint and its sites may be out of
    //  rel32 range ie bind_unreachable counts those.
    p = mapExecPages(cap);
  }
  ASS(p);
  _slabs.push_back({p, cap, 0, 0, inRegion});
  g_jitStats.slabsMapped++; g_jitStats.slabBytes += cap;
}

void* CopyPatchJit::slabAlloc(size_t size) {
  // Align to 16 bytes for instruction cache efficiency
  size = (size + 15) & ~15UL;
  ensureSlabSpace(size);
  ExecSlab& slab = _slabs.back();
  void* ptr = static_cast<char*>(slab.base) + slab.used;
  slab.used += size;
  slab.liveCount++;
  return ptr;
}

size_t CopyPatchJit::sizeClassIndex(size_t totalSize) {
  // Find the smallest class that fits totalSize
  for (size_t i = 0; i < NUM_SIZE_CLASSES; i++) {
    if (totalSize <= SIZE_CLASS_SIZES[i]) return i;
  }
  return NUM_SIZE_CLASSES; // oversized
}

size_t CopyPatchJit::sizeClassBucket(size_t classIdx, size_t totalSize) {
  if (classIdx < NUM_SIZE_CLASSES) return SIZE_CLASS_SIZES[classIdx];
  // Oversized: round up to 16-byte alignment
  return (totalSize + 15) & ~15UL;
}

CopyPatchJit::ExecSlab* CopyPatchJit::findSlab(void* ptr) {
  auto p = static_cast<char*>(ptr);
  for (auto& slab : _slabs) {
    auto base = static_cast<char*>(slab.base);
    if (p >= base && p < base + slab.capacity) {
      return &slab;
    }
  }
  return nullptr;
}

void* CopyPatchJit::allocExec(size_t userSize) {
  size_t totalSize = userSize + ALLOC_HEADER_SIZE;
  // Budget accounting: counts every allocation, recycled or not. Deliberately
  // conservative - a tree that frees and re-emits heavily still trips the
  // budget eventually, which is the safe direction to be wrong in.
  // Process-wide, so all trees draw on one budget.
  //
  //  NOTE: re-emission (JIT_REEMIT) charges this twice for a block it moves,
  //  because emittedTotal counts bytes ever emitted and is never credited back
  //  on a free.
  JitBudget::emittedTotal += totalSize;

  uint8_t* raw = nullptr;

  size_t classIdx = sizeClassIndex(totalSize);
  size_t bucket   = sizeClassBucket(classIdx, totalSize);

  // Try the free list for this size class
  if (classIdx < NUM_SIZE_CLASSES && _freeLists[classIdx]) {
    FreeNode* node  = _freeLists[classIdx];
    _freeLists[classIdx] = node->next;
    // The node pointer is the user-data region
    raw = reinterpret_cast<uint8_t*>(node) - ALLOC_HEADER_SIZE;
    // Re-mark the owning slab as having one more live allocation
    ExecSlab* slab = findSlab(raw);
    ASS(slab);
    slab->liveCount++;
  } else {
    // Bump-allocate from slab (slabAlloc increments liveCount)
    raw = static_cast<uint8_t*>(slabAlloc(bucket));
  }

  // Write the bucket size into the header so freeExec can find the class
  memcpy(raw, &bucket, sizeof(size_t));

  return raw + ALLOC_HEADER_SIZE;
}

void CopyPatchJit::freeExec(void* userPtr) {
  if (!userPtr) return;
  g_jitStats.frees++;

  uint8_t* raw = static_cast<uint8_t*>(userPtr) - ALLOC_HEADER_SIZE;

  // Read the bucket size from the header
  size_t bucket;
  memcpy(&bucket, raw, sizeof(size_t));

  // Decrement the owning slab's live count
  ExecSlab* slab = findSlab(raw);
  ASS(slab);
  ASS(slab->liveCount > 0);
  slab->liveCount--;

  // If the slab is completely dead, we could madvise it here.
  // For now we just let it sit-the free lists reclaim the space
  // for future allocations, and releaseAll() handles final cleanup.

  // Push onto the free list for the matching size class
  size_t classIdx = sizeClassIndex(bucket);
  if (classIdx < NUM_SIZE_CLASSES) {
    FreeNode* node = static_cast<FreeNode*>(userPtr);
    node->next = _freeLists[classIdx];
    _freeLists[classIdx] = node;
  }
  // Oversized allocations (classIdx == NUM_SIZE_CLASSES) are not
  // recycled individually-they contribute to slab-level reclamation
}

CopyPatchJit::CopyPatchJit() = default;

CopyPatchJit::~CopyPatchJit() {
  releaseAll();
}

void CopyPatchJit::releaseAll() {
  // Clear the free lists first (they point into the slabs we're about to unmap)
  for (size_t i = 0; i < NUM_SIZE_CLASSES; i++) {
    _freeLists[i] = nullptr;
  }

  for (auto& slab : _slabs) {
    if (slab.inRegion) {
      //  Hand it back to the shared pool rather than unmapping: the region is
      //  process-wide and other trees may still be using other parts of it.
      g_freeSlabs.push_back({slab.base, slab.capacity});
    } else {
      unmapExecPages(slab.base, slab.capacity);
    }
  }
  _slabs.clear();
  //  The shared region itself is never unmapped - it outlives every
  //  CopyPatchJit and costs nothing beyond untouched address space.
  if (_trampolineBase) {
    sharedRuntime().release(_trampolineBase);
    _trampolineBase = nullptr;
  }
  _trampoline = nullptr;
  _backtrackHandler = nullptr;
  _successHandler = nullptr;
  _totalFailHandler = nullptr;
  _expandStub = nullptr;
  _lazyCompileStub = nullptr;
  _bindJmpAltStub = nullptr;
  _ssDispatchStub = nullptr;
  _deoptStub = nullptr;
  _exitHandler = nullptr;
  _bailoutHandler = nullptr;
  //  JitBudget::emittedTotal is deliberately NOT reset: it is the process-wide budget
  //  counter, and space handed back here goes to g_freeSlabs rather than
  //  disappearing. Resetting it would let a run that churns trees emit
  //  without bound.
  _initialized = false;
}

void CopyPatchJit::freeCode(void* mcodePtr) {
  freeExec(mcodePtr);
}

//  ONE-TIME INITIALIZATION
void CopyPatchJit::initialize() {
  if (_initialized) return;

  compileTrampoline();
  compileExpandStub();
  compileLazyCompileStub();
  compileBindJmpAltStub();
  compileSsDispatchStub();
  compileDeoptStub();

  //  Two variants of every stencil: [0] for ops with no alternative, [1] for
  //  ops that have one. The no-alt variant omits the pushAlt block entirely
  //  and collapses each jmpAlt site to a bare backtrack jump. emitBlock picks
  //  per op on op.alternative().
  //  ... and two of every one of those again for the block HEAD, which
  //  carries the block-entry counter inside the stencil. Without
  //  JIT_RATE_COUNTERS the head variant is byte-identical to the non-head one,
  //  so the default build pays nothing for the extra dimension beyond 14 more
  //  Stencil objects built once here.
  for (unsigned v = 0; v < 2; v++) {
    const bool hasAlt = (v != 0);
    for (unsigned hd = 0; hd < 2; hd++) {
      const bool isHead = (hd != 0);
      compileStencilSuccessOrFail(hasAlt, isHead);
      compileStencilCheckGroundTerm(hasAlt, isHead);
      compileStencilLitEnd(hasAlt, isHead);
      compileStencilCheckFun(hasAlt, isHead);
      compileStencilAssignVar(hasAlt, isHead);
      compileStencilCheckVar(hasAlt, isHead);
    }
  }
  // _stencils[*][*][SEARCH_STRUCT] is left empty-SearchStructs are handled
  // differently (they're compiled individually, not via stencils).
  static bool dumped = false;
  if (!dumped && std::getenv("JIT_DUMP_STENCILS")) {
    dumped = true;
    static const char* nm[7] = {
      "SUCCESS_OR_FAIL", "CHECK_GROUND_TERM", "LIT_END",
      "CHECK_FUN", "ASSIGN_VAR", "CHECK_VAR", "SEARCH_STRUCT"
    };
    for (unsigned v = 0; v < 2; v++)
    for (unsigned hd = 0; hd < 2; hd++)
    for (unsigned i = 0; i < 7; i++) {
      const Stencil& st = _stencils[v][hd][i];
      if (st.code.empty()) continue;
      int trail = -1;
      for (const auto& h : st.holes)
        if (h.kind == StencilHole::NEXT_REL32 && size_t(h.offset) + 4 == st.code.size())
          trail = static_cast<int>(h.offset);
      std::fprintf(stderr,
        "%% STENCIL %-18s alt=%u head=%u bytes=%zu holes=%zu alt_holes=%u trailing_jmp_at=%d\n",
        nm[i], v, hd, st.code.size(), st.holes.size(),
        static_cast<unsigned>(st.altHoleCount), trail);
      for (size_t b = 0; b < st.code.size(); b++)
        std::fprintf(stderr, "%02x%c", st.code[b], ((b + 1) % 16) ? ' ' : '\n');
      std::fprintf(stderr, "\n");
    }
  }

  _initialized = true;
  g_jitStats.jitInstances++;
}



//  TRAMPOLINE: entry stub + backtrack loop + success/fail handlers
//
//  Called as:  trampoline(JitExecContext* ctx)
//  The trampoline saves callee-saved regs, loads the JIT register file
//  from ctx, jumps to ctx->op->_mcode, and returns when a success or
//  total-failure handler fires.


void CopyPatchJit::compileTrampoline() {
  // We use asmjit for this one-time compilation.
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  Label entryL       = a.new_label();
  Label successL     = a.new_label();
  Label backtrackL   = a.new_label();
  Label totalFailL   = a.new_label();
  Label exitL        = a.new_label();
  Label bailoutL     = a.new_label();

  // --- Entry ---
  a.bind(entryL);
  // Save callee-saved registers (6 pushes + 1 scratch = 7 -> 16-byte aligned)
  a.push(rbp);
  a.push(rbx);
  a.push(r12);
  a.push(r13);
  a.push(r14);
  a.push(r15);
  a.push(rdi);          // save ctx pointer (scratch, but we need it after)
  a.mov(rbp, rdi);      // rbp = ctx

  // Load hot registers from JitExecContext
  a.mov(r12, qword_ptr(rbp, offsetof(JitExecContext, ftData)));
  a.mov(r13, qword_ptr(rbp, offsetof(JitExecContext, tp)));
  a.mov(r14, qword_ptr(rbp, offsetof(JitExecContext, bindings)));
  a.mov(r15, qword_ptr(rbp, offsetof(JitExecContext, btCursor)));
  a.mov(rbx, qword_ptr(rbp, offsetof(JitExecContext, btEnd)));

  // Dispatch: jump to op->_mcode (or backtrack if op is null)
  // A null ctx.op signals "resume from backtrack stack":used when
  // re-entering after a yield. The stack stores {tp, CodeOp*}, which C++ can
  // also read directly (same shape as the interpreter's BTPoint).
  a.mov(rax, qword_ptr(rbp, offsetof(JitExecContext, op)));
  a.test(rax, rax);
  a.jz(backtrackL);
  a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jz(backtrackL);
  a.jmp(rax);

  // --- Success handler ---
  // op is already stored in ctx by the stencil.
  a.bind(successL);
  a.mov(byte_ptr(rbp, offsetof(JitExecContext, matched)), 1);
  a.jmp(exitL);

  // --- Backtrack handler ---
  //  Pop a {tp, CodeOp*} pair and resume. The stack stores CodeOp pointers
  //  rather than code addresses (see emitPushAlt), so the _mcode load and the
  //  lazy-compile path live here: an alternative is compiled only if it is
  //  actually resumed, and the entries are in the same {tp, CodeOp*} form the
  //  interpreter's BTPoint uses.
  Label btHaveMcode = a.new_label();
  a.bind(backtrackL);
  a.cmp(byte_ptr(rbp, offsetof(JitExecContext, bailout)), 0);
  a.jnz(bailoutL);
  a.cmp(r15, qword_ptr(rbp, offsetof(JitExecContext, btBase)));
  a.je(totalFailL);
  a.sub(r15, 16);
  a.mov(r13, qword_ptr(r15, 0));    // tp
  a.mov(rcx, qword_ptr(r15, 8));    // alternative CodeOp*
  a.test(rcx, rcx);
  a.jz(backtrackL);                  // null entry -> keep backtracking
  //  Instrumentation: count resumed pops, which splits backtrack-dispatch
  //  traffic from jmpAlt-dispatch traffic.
  #if defined(JIT_RATE_COUNTERS) || defined(JIT_GATE_COUNTERS)
  a.inc(qword_ptr(rbp, offsetof(JitExecContext, btPops)));
  #endif
  a.mov(rax, qword_ptr(rcx, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jnz(btHaveMcode);
  //  Not compiled yet: rcx already holds the CodeOp*, which is the
  //  lazyCompileStub's argument convention. A null result means the block
  //  could not be compiled (budget), so keep backtracking rather than
  //  treating it as a match failure.
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.test(rax, rax);
  a.jz(backtrackL);
  a.bind(btHaveMcode);
  a.jmp(rax);

  // --- Bailout: the hard code budget was hit mid-match. Report "no match"
  //     and leave immediately; executeMachineCode sees ctx->bailout and
  //     throws from C++ frames, which (unlike these) have unwind info. ---
  a.bind(bailoutL);
  a.mov(byte_ptr(rbp, offsetof(JitExecContext, matched)), 0);
  a.jmp(exitL);

  // --- Total failure: try next literal or exit ---
  // Layout assumptions (look at static asserts at the start for validation):
  //   sizeof(LitInfo) == 24
  //   offsetof(LitInfo, ft) == 8
  //   FlatTerm::_data is at offset 8 from FlatTerm*
  a.bind(totalFailL);

  Label realFailL = a.new_label();

  // Increment curLInfo and check bounds
  a.mov(rax, qword_ptr(rbp, offsetof(JitExecContext, curLInfo)));
  a.inc(rax);
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, curLInfo)), rax);
  a.cmp(rax, qword_ptr(rbp, offsetof(JitExecContext, linfoCnt)));
  a.jae(realFailL);

  // Compute ftData = &(linfos[curLInfo].ft->_data[0])
  //   rcx = linfos + curLInfo * sizeof(LitInfo)
  //   rcx = rcx->ft                               (FlatTerm*)
  //   r12 = rcx + 8                                (&_data[0])
  static constexpr int32_t SIZEOF_LITINFO = 24;
  static constexpr int32_t OFS_LITINFO_FT = 8;
  static constexpr int32_t OFS_FLATTERM_DATA = 8;

  a.imul(rcx, rax, SIZEOF_LITINFO);
  a.add(rcx, qword_ptr(rbp, offsetof(JitExecContext, linfos)));
  a.mov(rcx, qword_ptr(rcx, OFS_LITINFO_FT));
  a.lea(r12, ptr(rcx, OFS_FLATTERM_DATA));

  // Reset tp = 0
  a.xor_(r13, r13);

  // Reset btCursor to btBase (empty backtrack stack for new literal)
  a.mov(r15, qword_ptr(rbp, offsetof(JitExecContext, btBase)));

  // Jump to tree entry point-start matching the new literal
  a.mov(rax, qword_ptr(rbp, offsetof(JitExecContext, entryMcode)));
  a.jmp(rax);

  // --- Real failure: all literals exhausted ---
  a.bind(realFailL);
  a.mov(byte_ptr(rbp, offsetof(JitExecContext, matched)), 0);

  // --- Exit: store state back to ctx, restore regs, ret ---
  a.bind(exitL);
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, tp)), r13);
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, btCursor)), r15);
  a.pop(rdi);
  a.pop(r15);
  a.pop(r14);
  a.pop(r13);
  a.pop(r12);
  a.pop(rbx);
  a.pop(rbp);
  a.ret();

  // --- Extract and install ---
  // The trampoline lives in JitRuntime-managed executable memory.
  void* ptr = nullptr;
  Error err = sharedRuntime().add(&ptr, &code);
  (void)err;
  ASS(err == Error::kOk);
  _trampolineBase = ptr;
  _trampolineSize = code.code_size();

  auto base = static_cast<char*>(ptr);
  _trampoline       = reinterpret_cast<TrampolineFunc>(base + code.label_offset(entryL));
  _backtrackHandler = base + code.label_offset(backtrackL);
  _successHandler   = base + code.label_offset(successL);
  _totalFailHandler = base + code.label_offset(totalFailL);
  _exitHandler      = base + code.label_offset(exitL);
  _bailoutHandler   = base + code.label_offset(bailoutL);

  // perf map: split the trampoline into its four regions so profiles
  // separate entry glue from backtrack/success/totalFail dispatch.
  {
    struct { size_t ofs; const char* name; } regs[] = {
      { code.label_offset(entryL),     "jit_tramp_entry"        },
      { code.label_offset(backtrackL), "jit_bt_handler"         },
      { code.label_offset(successL),   "jit_success_handler"    },
      { code.label_offset(totalFailL), "jit_totalfail_handler"  },
    };
    std::sort(std::begin(regs), std::end(regs),
              [](auto& x, auto& y) { return x.ofs < y.ofs; });
    for (size_t i = 0; i < 4; i++) {
      size_t end = (i + 1 < 4) ? regs[i+1].ofs : _trampolineSize;
      perfMapAdd(base + regs[i].ofs, end - regs[i].ofs, "%s", regs[i].name);
    }
  }
}

void CopyPatchJit::compileExpandStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  // On entry: rsp is 8 mod 16 (from caller's 'call')
  // save rdx, r10 because ASSIGN_VAR/CHECK_GROUND_TERM
  // keep them live across pushAlt (which contains this call site)
  a.push(rcx);    // save mcode
  a.push(rdx);    // save (live in ASSIGN_VAR)
  a.push(r10);    // save (live in ASSIGN_VAR/CHECK_GROUND_TERM) + align

  // store btCursor into ctx so C helper can see it
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, btCursor)), r15);

  // call expandBtBufferHelper(ctx)
  a.mov(rdi, rbp);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandBtFunc)));

  a.pop(r10);     // restore
  a.pop(rdx);     // restore
  a.pop(rcx);     // restore

  // reload r15, rbx-buffer may have been reallocated
  a.mov(r15, qword_ptr(rbp, offsetof(JitExecContext, btCursor)));
  a.mov(rbx, qword_ptr(rbp, offsetof(JitExecContext, btEnd)));

  a.ret();

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _expandStub = dest;
  perfMapAdd(dest, bytes.size(), "jit_expand_stub");
}

/*
 * compileLazyCompileStub- called from pushAlt and the shared SS dispatch stub
 * when a CodeOp has null _mcode. Bridges into the C++ lazyCompileHelper.
 * (jmpAlt sites no longer use this stub, they go through bindJmpAltStub.)
 *
 * On entry from stencil:
 *   rcx = CodeOp* (the uncompiled alternative)
 *   rsp is 8 mod 16 (from caller's 'call' instruction)
 *
 * On return:
 *   rax = _mcode (non-null if compiled) or nullptr
 *   rdx, r10 preserved
 *   rcx clobbered
 */
void CopyPatchJit::compileLazyCompileStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  // On entry: rsp is 8 mod 16 (from caller's 'call')
  // 3 pushes->rsp goes to (8+24) mod 16 = 0 mod 16->aligned for inner call
  a.push(rcx);     // save CodeOp*
  a.push(rdx);     // save (live in ASSIGN_VAR)
  a.push(r10);     // save (live in ASSIGN_VAR/CHECK_GROUND_TERM) + aligns stack

  // Set up args for lazyCompileHelper(ctx, codeOp*)
  a.mov(rsi, rcx);    // arg2 = CodeOp*
  a.mov(rdi, rbp);    // arg1 = ctx
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileFunc)));   // stack: 0 mod 16

  a.pop(r10);      // restore
  a.pop(rdx);      // restore
  a.pop(rcx);      // restore

  a.ret();

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _lazyCompileStub = dest;
  perfMapAdd(dest, bytes.size(), "jit_lazy_compile_stub");
}

/*
 * compileBindJmpAltStub - the PLT-style binder entered from initial-form
 * jmpAlt sites via 'call [rbp + bindJmpAltStub]'.
 *
 * On entry:
 *   rax   = CodeOp* alternative (non-null; the site's jz filtered null)
 *   [rsp] = return address = siteHead + s_jmpAltRetOfs (identifies the site)
 *   rsp is 8 mod 16
 *
 * The stub never returns to the site: it calls bindJmpAltHelper (which
 * compiles the target if needed and patches the site to 'jmp rel32' when
 * safe), discards the return address, and tail-jumps to the target - or to
 * the backtrack handler if the helper yields nullptr. rdx/r10 are preserved
 * for symmetry with lazyCompileStub; nothing else is live across a taken
 * jmpAlt (the target block rederives everything from the register file).
 */
void CopyPatchJit::compileBindJmpAltStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  // 3 pushes: 8 - 24 = -16 == 0 mod 16 -> aligned for the inner call
  a.push(rcx);
  a.push(rdx);
  a.push(r10);

  a.mov(rsi, rax);                       // arg2 = CodeOp* alternative
  a.mov(rdx, qword_ptr(rsp, 24));        // arg3 = return address (under the 3 pushes)
  a.mov(rdi, rbp);                       // arg1 = ctx
  a.call(qword_ptr(rbp, offsetof(JitExecContext, bindJmpAltFunc)));

  a.pop(r10);
  a.pop(rdx);
  a.pop(rcx);
  a.add(rsp, 8);                         // discard return address - we never return

  a.test(rax, rax);
  Label toBt = a.new_label();
  a.jz(toBt);
  a.jmp(rax);
  a.bind(toBt);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, backtrackHandler)));

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _bindJmpAltStub = dest;
  perfMapAdd(dest, bytes.size(), "jit_bind_stub");
}

/*
 * compileSsDispatchStub: the shared body of every SearchStruct, compiled
 * once. Entered by 'jmp' from a 16-byte per-SS landing stub with
 * rdi = &ss->landingOp and rsp in trampoline steady state (0 mod 16).
 *
 * Semantics (net-effect equivalent to the interpreter's SEARCH_STRUCT):
 *   target = lookup(key at ft[tp])
 *   found:     push {tp, alternative CodeOp*} if landingOp has one,
 *              then jump to target's code (which re-verifies the key itself)
 *   not found: jump to the alternative directly (nothing was pushed), or
 *              backtrack if there is none
 * The interpreter pushes the alternative first and pops it on failure; the
 * two orderings are observationally identical and this one skips the
 * push/pop round trip on the miss path.
 */
/*
 * emitSsDispatchTail - everything after the lookup, shared by both SS stubs.
 * Entry: rdi = &ss->landingOp, rax = target CodeOp* or 0.
 * Never returns: jumps to the target's code, the alternative's code, or the
 * backtrack handler.
 */
void CopyPatchJit::emitSsDispatchTail(void* asm_ptr)
{
  auto& a = *static_cast<Assembler*>(asm_ptr);

  Label notFound = a.new_label();
  Label doPush   = a.new_label();
  Label dispatch = a.new_label();
  Label go       = a.new_label();
  Label goAlt    = a.new_label();
  Label bt       = a.new_label();

  a.test(rax, rax);
  a.jz(notFound);

  // --- FOUND: rax = target CodeOp* ---
  a.mov(rdx, rax);          // rdx = target (survives lazyCompileStub/expandStub)
  a.mov(rax, qword_ptr(rdi, offsetof(CodeTree::CodeOp, _alternative)));
  a.test(rax, rax);
  a.jz(dispatch);
  a.mov(rcx, rax);
  a.cmp(r15, rbx);
  a.jb(doPush);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));
  a.bind(doPush);
  a.mov(qword_ptr(r15, 0), r13);
  a.mov(qword_ptr(r15, 8), rcx);
  a.add(r15, 16);
  a.bind(dispatch);
  a.mov(rax, qword_ptr(rdx, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jnz(go);
  a.mov(rcx, rdx);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.test(rax, rax);
  a.jz(bt);                 // pushed alt (if any) is popped by backtrack
  a.bind(go);
  a.jmp(rax);

  // --- NOT FOUND: nothing pushed -> alternative directly, or backtrack ---
  a.bind(notFound);
  a.mov(rax, qword_ptr(rdi, offsetof(CodeTree::CodeOp, _alternative)));
  a.test(rax, rax);
  a.jz(bt);
  a.mov(rcx, rax);
  a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jnz(goAlt);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.test(rax, rax);
  a.jz(bt);
  a.bind(goAlt);
  a.jmp(rax);

  a.bind(bt);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, backtrackHandler)));
}

void CopyPatchJit::compileSsDispatchStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  // --- lookup: rax = ssLookupHelper(ctx, landingOp, ftData, tp) ---
  // Steady-state rsp is 0 mod 16; two pushes keep it 0 mod 16 at the call.
  // The second push doubles as the save slot for rdi (landingOp*).
  a.push(rdi);
  a.push(rdi);
  a.mov(rdx, r12);          // arg3 = ftData   (live register, ctx copy is stale)
  a.mov(rcx, r13);          // arg4 = tp
  a.mov(rsi, rdi);          // arg2 = landingOp
  a.mov(rdi, rbp);          // arg1 = ctx
  a.call(qword_ptr(rbp, offsetof(JitExecContext, ssLookupFunc)));
  a.pop(rdi);
  a.pop(rdi);               // rdi = landingOp again

  emitSsDispatchTail(&a);

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _ssDispatchStub = dest;
  perfMapAdd(dest, bytes.size(), "jit_ss_dispatch_stub");
}

/*
 * compileDeoptStub - the hand-back to the interpreter.
 *
 * lazyCompileBlock returns this address instead of compiling when a block has
 * not yet been entered often enough to be worth emitting (see
 * JIT_TIER_THRESHOLD). Whichever site was resolving the block - pushAlt's pop
 * path, the bind stub, the SS dispatch stub - then jumps here exactly as it
 * would to real code.
 *
 * The helper has already stored the CodeOp* to resume at in ctx->op, so all
 * this has to do is flush the two registers C++ cannot see (tp, btCursor),
 * raise the deopt flag, and leave through the trampoline's normal epilogue.
 * The backtrack stack is left exactly as it is: entries are {tp, CodeOp*},
 * i.e. BTPoints, so executeMachineCode can hand them straight to the
 * interpreter.
 *
 * Note this is entered by jmp, not call - there is no return address and
 * nothing to unwind.
 */
void CopyPatchJit::compileDeoptStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  a.mov(qword_ptr(rbp, offsetof(JitExecContext, tp)), r13);
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, btCursor)), r15);
  a.mov(byte_ptr(rbp, offsetof(JitExecContext, deopt)), 1);
  a.mov(byte_ptr(rbp, offsetof(JitExecContext, matched)), 0);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, exitHandler)));

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _deoptStub = dest;
  _deoptStubAddr = dest;
  perfMapAdd(dest, bytes.size(), "jit_deopt_stub");
}

/*
 * Emits:
 *   movabs rcx, <CodeOp* alt>   ; 10 bytes-patchable
 *   test   rcx, rcx
 *   jz     .noPush
 *   mov    rdi, rcx             ; save CodeOp* for potential lazy compile
 *   mov    rcx, [rcx + _mcode]  ; dereference to mcode
 *   test   rcx, rcx
 *   jnz    .haveMcode
 *   ; _mcode null -> lazy compile via stub
 *   mov    rcx, rdi             ; pass CodeOp* in rcx (stub convention)
 *   call   [rbp + lazyCompileStub]
 *   mov    rcx, rax             ; result in rcx
 *   test   rcx, rcx
 *   jz     .noPush
 *   .haveMcode:
 *   cmp    r15, rbx             ; btCursor >= btEnd?
 *   jb     .doPush
 *   call   [rbp + expandStub]   ; cold: expand buffer, reload r15/rbx
 *   .doPush:
 *   mov    [r15+0], r13         ; tp
 *   mov    [r15+8], rcx         ; alternative CodeOp*
 *   add    r15, 16
 *   .noPush:
 *
 * Hot-path clobbers: rcx, rdi.   rax is UNTOUCHED on hot path.
 * Cold-path clobbers: rax, rcx, rdi, rsi (via call)
 *
 * pushAlt is deliberately NOT bound: it resolves _mcode at push time, and the
 * pushed value lives only within one trampoline invocation, so it stays
 * correct under index mutation without any patching protocol.
 only rcx, rdx, r10 survive; rax and r11 do not
 */
void CopyPatchJit::emitPushAlt(void* asm_ptr, Stencil& s, size_t base, bool hasAlt) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

  //  NO-ALT VARIANT: the op has no alternative, so there is nothing to push.
  //  Emit nothing at all. This removes the movabs (10 B), the test/jz (9 B)
  //  and the whole bounds-checked push (23 B) - 42 bytes and three executed
  //  instructions per site. 99.9% of emitted alt slots are null, so this is
  //  the variant almost every op takes.
  if (!hasAlt) return;

  size_t immOfs = emitMovAbsRcx(a, PH_ALT2) - base;
  s.holes.push_back({StencilHole::ALT_PTR_PUSH, static_cast<uint16_t>(immOfs)});
  s.altHoleCount++;

  Label noPush = a.new_label();
  Label doPush = a.new_label();

  a.test(rcx, rcx);
  a.jz(noPush);

  //  Push the CodeOp* itself, NOT its _mcode. Two reasons:
  //    1. the entry becomes interpretable by the interpreter as well as by
  //       JIT code, which is what lets a suspended match be handed over
  //       (BTPoint is {tp, CodeOp*} too), and
  //    2. resolving _mcode - and lazily compiling when it is null - moves off
  //       this hot path and onto the backtrack handler, which pops far less
  //       often than pushAlt pushes (594 k pops against billions of edges on
  //       HWV069+1). The alternative is only ever compiled if it is actually
  //       resumed.
  a.cmp(r15, rbx);
  a.jb(doPush);

  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));

  a.bind(doPush);
  a.mov(qword_ptr(r15, 0), r13);     // tp
  a.mov(qword_ptr(r15, 8), rcx);     // alternative CodeOp*
  a.add(r15, 16);

  a.bind(noPush);
}

/*
 * jmpAlt site - PLT-style lazily bound alternative dispatch.
 *
 * INITIAL form (as emitted; site start == movabs start):
 *   +0   movabs rax, <CodeOp* alt>        ; 10 bytes; ALT_PTR hole at +2
 *   +10  test   rax, rax
 *        jz     .bt                        ; null alternative -> backtrack
 *        call   [rbp + bindJmpAltStub]     ; never returns: binds site, jumps on
 *   .bt: jmp    [rbp + backtrackHandler]
 *
 * BOUND form (installed by bindJmpAltHelper):
 *   +0   jmp rel32 <target mcode>          ; overwrites the movabs head;
 *                                          ; resolved at decode - no BTB, no
 *                                          ; dependent loads, fetch streams on
 *   (+5..+9 dead imm tail; rest of the site unreachable but intact)
 *
 * patchAlternative restores the initial head (48 B8) whenever the op's
 * alternative changes, so index mutation never reasons about bound sites.
 *
 * This replaces the old inline mcode-load + 'jmp rax' sequence; the initial
 * form is also ~15-19 bytes smaller per site.
 *
 * Clobbers (either form/path): rax, rcx, rdi, rsi.
 */
void CopyPatchJit::emitJmpAlt(void* asm_ptr, Stencil& s, size_t base, bool hasAlt) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

  //  NO-ALT VARIANT: a null alternative means this path backtracks
  //  unconditionally, so the whole site collapses to the jump the site would
  //  have fallen through to anyway - 3 bytes instead of 25. The jump MUST
  //  still be emitted: it is the entire fail path.
  if (!hasAlt) {
    a.jmp(qword_ptr(rbp, offsetof(JitExecContext, backtrackHandler)));
    return;
  }

  size_t siteStart = a.offset();
  size_t immOfs = emitMovAbsRax(a, PH_ALT1) - base;
  s.holes.push_back({StencilHole::ALT_PTR, static_cast<uint16_t>(immOfs)});
  s.altHoleCount++;

  Label bt = a.new_label();
  a.test(rax, rax);
  a.jz(bt);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, bindJmpAltStub)));
  size_t retOfs = a.offset() - siteStart;
  if (s_jmpAltRetOfs == 0) {
    s_jmpAltRetOfs = retOfs;
  }
  ASS_EQ(s_jmpAltRetOfs, retOfs);   // all sites must share one byte layout
  a.bind(bt);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, backtrackHandler)));
}

/*
 * emitNextJump-jmp rel32 to the next stencil
 * The rel32 is a PLACEHOLDER that gets patched at layout time
 */
void CopyPatchJit::emitNextJump(void* asm_ptr, Stencil& s, size_t base) {
  auto& a = *static_cast<Assembler*>(asm_ptr);
  // Emit: E9 <rel32>  (5 bytes total)
  // The rel32 placeholder will be overwritten at layout time.
  size_t jmpOfs = a.offset() - base;
  uint8_t jmpBuf[5] = { 0xE9 };
  memcpy(jmpBuf + 1, &PH_NEXT32, 4);
  a.embed(jmpBuf, 5);
  // Record the hole at offset+1 (the 4-byte immediate after the E9 opcode)
  s.holes.push_back({StencilHole::NEXT_REL32, static_cast<uint16_t>(jmpOfs + 1)});
}

void CopyPatchJit::compileStencilCheckFun(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::CHECK_FUN];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  // Load ft[tp]
  a.lea(rax, ptr(r12, r13, 3));       // rax = &ftData[tp]
  a.mov(r11, qword_ptr(rax));         // r11 = entry._content

  // Check tag == FUN(1) or FUN_UNEXPANDED(4)
  a.mov(rdx, r11);
  a.and_(rdx, 7);                      // tag
  Label tagOk = a.new_label();
  Label notFun = a.new_label();
  a.cmp(rdx, FlatTerm::FUN);
  a.je(tagOk);
  a.cmp(rdx, FlatTerm::FUN_UNEXPANDED);
  a.jne(notFun);
  a.bind(tagOk);

  // Extract functor number: (content >> 3) & 0x1FFFFFFF
  a.mov(rdx, r11);
  a.shr(rdx, 3);
  a.and_(edx, 0x1FFFFFFFu);

  // Compare with the functor-4-byte immediate, patchable
  size_t funcOfs = a.offset() - base + 2;  // cmp edx, imm32 is [81 FA <imm32>]
  a.cmp(edx, PH_FUNC);
  Label matched = a.new_label();
  a.je(matched);

  // --- Mismatch: jmpAlt ---
  a.bind(notFun);
  emitJmpAlt(&a, s, base, hasAlt);

  // --- Match: expand if needed, pushAlt, advance, fall through ---
  a.bind(matched);

  // If tag was FUN_UNEXPANDED, call expand
  a.test(r11, 4);
  Label noExpand = a.new_label();
  a.jz(noExpand);
  // call expandEntryHelper(&ft[tp])
  a.mov(rdi, rax);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandEntryFunc)));
  a.bind(noExpand);

  emitPushAlt(&a, s, base, hasAlt);
  a.add(r13, FlatTerm::FUNCTION_ENTRY_COUNT);
  emitNextJump(&a, s, base);

  // Record the functor hole
  s.holes.push_back({StencilHole::FUNCTOR_IMM32, static_cast<uint16_t>(funcOfs)});

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilCheckGroundTerm(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::CHECK_GROUND_TERM];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  // Load ft[tp]
  a.lea(rax, ptr(r12, r13, 3));
  a.mov(r11, qword_ptr(rax));
  a.mov(rdx, r11);
  a.and_(rdx, 7);
  Label tagOk = a.new_label();
  Label notFun = a.new_label();
  a.cmp(rdx, FlatTerm::FUN);
  a.je(tagOk);
  a.cmp(rdx, FlatTerm::FUN_UNEXPANDED);
  a.jne(notFun);
  a.bind(tagOk);

  // Compare Term* at ft[tp+1] with the target term
  // Target term is an 8-byte immediate, patchable
  size_t termOfs = emitMovAbsRdx(a, PH_GTERM) - base;
  s.holes.push_back({StencilHole::GROUND_TERM_PTR, static_cast<uint16_t>(termOfs)});

  a.cmp(rdx, qword_ptr(rax, 8));     // compare with FUN_TERM_PTR entry
  Label matched = a.new_label();
  a.je(matched);

  a.bind(notFun);
  emitJmpAlt(&a, s, base, hasAlt);

  a.bind(matched);
  // Load FUN_RIGHT_OFS: (ft[tp+2]._content >> 3) & 0x1FFFFFFF
  a.mov(r10, qword_ptr(rax, 16));
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);
  emitPushAlt(&a, s, base, hasAlt);
  a.add(r13, r10);
  emitNextJump(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilAssignVar(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::ASSIGN_VAR];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  // Load ft[tp]
  a.lea(rax, ptr(r12, r13, 3));
  a.mov(r11, qword_ptr(rax));
  a.mov(rdx, r11);
  a.and_(rdx, 7);
  Label funCase = a.new_label();
  a.cmp(rdx, FlatTerm::VAR);
  a.jne(funCase);

  // ---- Variable case ----
  // Construct TermList for var: (number << 2) | 1

  a.mov(rdx, r11);
  a.shr(rdx, 3);
  a.and_(edx, 0x1FFFFFFFu);
  a.shl(rdx, 2);
  a.or_(rdx, 1);

  emitPushAlt(&a, s, base, hasAlt);

  // Store to bindings[var].  The byte offset is a 4-byte immediate.
  // We use 'mov [r14 + disp32], rdx'-the disp32 is patchable.
  // Encoding: REX.W + 89 + ModRM(10,rdx,r14) + SIB(none) + disp32
  //   = 49 89 96 <disp32>
  {
    size_t varOfs = a.offset() - base + 3;  // disp32 starts at byte 3 of the instruction
    uint8_t inst[7] = { 0x49, 0x89, 0x96 };
    uint32_t ph = PH_VAROFS;
    memcpy(inst + 3, &ph, 4);
    a.embed(inst, 7);
    s.holes.push_back({StencilHole::VAR_BYTE_OFS, static_cast<uint16_t>(varOfs)});
  }

  a.inc(r13);
  // Jump over the fun-case to the next stencil
  emitNextJump(&a, s, base);

  // ---- Function case ----
  a.bind(funCase);
  // Load Term* from ft[tp+1] and FUN_RIGHT_OFS from ft[tp+2] BEFORE pushAlt
  // (pushAlt clobbers rax, rcx)
  a.mov(rdx, qword_ptr(rax, 8));      // Term* (FUN_TERM_PTR)
  a.mov(r10, qword_ptr(rax, 16));
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);          // FUN_RIGHT_OFS

  emitPushAlt(&a, s, base, hasAlt);

  // Store binding (rdx and r10 survive pushAlt-only rax,rcx clobbered)
  {
    size_t varOfs = a.offset() - base + 3;
    uint8_t inst[7] = { 0x49, 0x89, 0x96 };
    uint32_t ph = PH_VAROFS;
    memcpy(inst + 3, &ph, 4);
    a.embed(inst, 7);
    s.holes.push_back({StencilHole::VAR_BYTE_OFS, static_cast<uint16_t>(varOfs)});
  }

  a.add(r13, r10);
  // Fall through to next stencil
  emitNextJump(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilCheckVar(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::CHECK_VAR];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  // Load the existing binding from bindings[var]
  {
    // mov rdx, [r14 + disp32]  ->  49 8B 96 <disp32>
    size_t varOfs = a.offset() - base + 3;
    uint8_t inst[7] = { 0x49, 0x8B, 0x96 };
    uint32_t ph = PH_VAROFS;
    memcpy(inst + 3, &ph, 4);
    a.embed(inst, 7);
    s.holes.push_back({StencilHole::VAR_BYTE_OFS, static_cast<uint16_t>(varOfs)});
  }

  // Load ft[tp]
  a.lea(rax, ptr(r12, r13, 3));
  a.mov(r11, qword_ptr(rax));
  a.mov(r10, r11);
  a.and_(r10, 7);
  Label funCase = a.new_label();
  a.cmp(r10, FlatTerm::VAR);
  a.jne(funCase);

  // ---- Variable case ----
  // Construct TermList for var and compare with binding
  a.mov(r10, r11);
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);
  a.shl(r10, 2);
  a.or_(r10, 1);
  Label varMatched = a.new_label();
  a.cmp(r10, rdx);
  a.je(varMatched);
  // Mismatch
  emitJmpAlt(&a, s, base, hasAlt);
  a.bind(varMatched);
  emitPushAlt(&a, s, base, hasAlt);
  a.inc(r13);
  emitNextJump(&a, s, base);

  // ---- Function case ----
  a.bind(funCase);
  a.mov(r10, qword_ptr(rax, 8));      // Term*
  Label funMatched = a.new_label();
  a.cmp(r10, rdx);
  a.je(funMatched);
  emitJmpAlt(&a, s, base, hasAlt);
  a.bind(funMatched);
  // Load FUN_RIGHT_OFS into r10 before pushAlt
  a.mov(r10, qword_ptr(rax, 16));
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);
  emitPushAlt(&a, s, base, hasAlt);
  a.add(r13, r10);
  emitNextJump(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilSuccessOrFail(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::SUCCESS_OR_FAIL];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  // Load op._content via op pointer
  size_t opOfs = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfs)});

  a.mov(rdx, qword_ptr(rax, 0));      // rdx = _content
  Label isSuccess = a.new_label();
  a.test(rdx, rdx);
  a.jnz(isSuccess);

  // Fail: jmpAlt
  emitJmpAlt(&a, s, base, hasAlt);

  // Success:
  a.bind(isSuccess);
  // Check curLInfo == 0
  a.mov(rcx, qword_ptr(rbp, offsetof(JitExecContext, curLInfo)));
  Label notFirstRound = a.new_label();
  a.test(rcx, rcx);
  a.jnz(notFirstRound);

  // First round: pushAlt, then yield success
  emitPushAlt(&a, s, base, hasAlt);

  // Store op ptr into ctx
  size_t opOfs2 = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfs2)});
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, op)), rax);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, successHandler)));

  // Not first round? ->backtrack
  a.bind(notFirstRound);
  emitJmpAlt(&a, s, base, hasAlt);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilLitEnd(bool hasAlt, bool isHead) {
  Stencil& s = _stencils[hasAlt][isHead][CodeTree::LIT_END];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();
  if (isHead) emitBlockHeadCounter(a, s, base);
  emitOpsExecInc(a);

  size_t opOfsChk = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfsChk)});
  a.mov(rdx, qword_ptr(rax, 0));
  Label notFail = a.new_label();
  a.test(rdx, rdx);
  a.jnz(notFail);
  emitJmpAlt(&a, s, base, hasAlt);

  a.bind(notFail);

  emitPushAlt(&a, s, base, hasAlt);

  // Store op ptr into ctx
  size_t opOfs = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfs)});
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, op)), rax);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, successHandler)));

  s.code = extractCode(code);
}

//  --- BLOCK EMISSION ---
//
//  For each op in the block:
//    1. memcpy the stencil bytes to the output buffer, ELIDING the
//       trailing jmp-to-next for non-last ops (zero-cost fall-through)
//    2. Patch all holes with actual values
//    3. Record _mcode and _altPatchOfs on the CodeOp
//

void CopyPatchJit::emitBlock(CodeTree::CodeBlock* block) {
  ASS(_initialized);

  size_t nOps = block->length();
  if (nOps == 0) return;


  // --- Helper: find the trailing NEXT_REL32 hole in a stencil ---
  // Returns the hole's rel32 offset, or -1 if the stencil has no NEXT_REL32.
  // The trailing jmp is the one with the highest offset (last emitted).
  //  Which stencil variant an op takes. MUST be the same expression in
  //  phase 1 (sizing) and phase 3 (copying): if they disagree, the computed
  //  block size and the bytes written diverge and the code is corrupt.
  //  op.alternative() cannot change inside this function.
  auto variantOf = [](CodeTree::CodeOp& o) -> unsigned {
    return o.alternative() != nullptr ? 1u : 0u;
  };

  auto findTrailingNextOfs = [](const Stencil& st) -> int {
    int maxOfs = -1;
    for (const auto& h : st.holes) {
      if (h.kind == StencilHole::NEXT_REL32 && static_cast<int>(h.offset) > maxOfs) {
        maxOfs = static_cast<int>(h.offset);
      }
    }
    return maxOfs;
  };

  // --- Phase 1: calculate total code size ---
  // For non-last ops, the trailing 5-byte jmp (E9 rel32) is elided because
  // the next stencil is laid out contiguously
  // Only the last op keeps its trailing jmp (to the BT stub)
  static constexpr size_t BT_STUB_SIZE = 6;

  // static constexpr size_t JMP_SIZE = 5;       // E9 <rel32>

  size_t totalSize = BT_STUB_SIZE;
  for (size_t i = 0; i < nOps; i++) {
    CodeTree::CodeOp& op = (*block)[i];
    unsigned instr = op._instruction();
    ASS(instr != CodeTree::SEARCH_STRUCT);
    const Stencil& st = _stencils[variantOf(op)][i == 0][instr];
    size_t sz = st.code.size();
    if (i + 1 < nOps) {
      // Elide trailing jmp if present
      int trailOfs = findTrailingNextOfs(st);
      if (trailOfs >= 0) {
        sz = static_cast<size_t>(trailOfs) - 1;  // exclude E9 byte and rel32
      }
    }
    totalSize += sz;
  }

    // --- Phase 2: allocate contiguous executable memory ---
  uint8_t* buf = static_cast<uint8_t*>(allocExec(totalSize));
  size_t cursor = 0;
  g_jitStats.emitBlocks++; g_jitStats.emitBytes += totalSize; g_jitStats.emitOps += nOps;

  //  Record the block's true base. CodeOp::_mcode is not a substitute: the
  //  out-of-line patch path in patchAlternative can repoint the HEAD's _mcode
  //  at a standalone copy, after which _mcode no longer locates this
  //  allocation. freeJitBlock and the re-layout pass both read this instead.
  g_blockBase[&(*block)[0]] = buf;

  // --- Phase 3: copy-and-patch each op ---
  for (size_t i = 0; i < nOps; i++) {
    CodeTree::CodeOp& op = (*block)[i];
    unsigned instr = op._instruction();
    const unsigned var = variantOf(op);
    //  i == 0 picks the head variant, which carries the block-entry counter.
    //  MUST match phase 1's index expression exactly or the sized and written
    //  byte counts diverge and the block is corrupt.
    const Stencil& st = _stencils[var][i == 0][instr];
    bool isLast = (i + 1 == nOps);
 
    // Determine the trailing NEXT_REL32 offset and copy size.
    int trailingNextOfs = findTrailingNextOfs(st);
    size_t copySize;
    if (!isLast && trailingNextOfs >= 0) {
      // Elide trailing jmp: copy up to (but not including) the E9 opcode
      copySize = static_cast<size_t>(trailingNextOfs) - 1;
    } else {
      copySize = st.code.size();
    }
 
    // (a) Copy stencil bytes
    uint8_t* dest = buf + cursor;
    memcpy(dest, st.code.data(), copySize);
    g_jitStats.emitOpsByKind[instr]++;
    g_jitStats.emitBytesByKind[instr] += copySize;
 
    // Record _mcode
    op._mcode = dest;
 
    // Reset patch offsets
    for (int j = 0; j < 4; j++) {
      op._altPatchOfs[j] = CodeTree::CodeOp::ALT_PATCH_NONE;
    }

    //  No-alt variant: this body has no ALT holes, so all four slots stay
    //  free. Tag slot 0, and stash the op's emitted size in slot 3 - that is
    //  the only thing patchAlternative needs to locate this op's successor if
    //  an alternative turns up later, because ops are laid out contiguously
    //  and the BT stub follows the last one.
    if (var == 0) {
      op._altPatchOfs[0] = ALT_NOALT_TAG;
      op._altPatchOfs[3] = static_cast<uint16_t>(copySize);
      //  Slot 1 carries this op's index within its block, which is what lets
      //  patchAlternative find the block HEAD from an interior op and queue the
      //  whole block for re-emission (JIT_REEMIT). Slots 1 and 2 are unused in
      //  the tagged form. 0xFFFF and 0xFFFE are taken as sentinels, so an index
      //  that does not fit is recorded as unknown and the caller falls back to
      //  the out-of-line patch.
      op._altPatchOfs[1] = (i <= 0xFFFDu)
                             ? static_cast<uint16_t>(i)
                             : CodeTree::CodeOp::ALT_PATCH_NONE;
    }

    // (b) Patch holes
    int altPatchIdx = 0;
    for (const auto& hole : st.holes) {
      // Skip the trailing NEXT_REL32 hole if we elided it
      if (hole.kind == StencilHole::NEXT_REL32
          && static_cast<int>(hole.offset) == trailingNextOfs
          && !isLast) {
        continue;
      }

      // Skip any hole whose offset falls outside the copied region
      if (hole.offset >= copySize && hole.kind != StencilHole::NEXT_REL32) {
        continue;
      }

      uint8_t* target = dest + hole.offset;

      switch (hole.kind) {
        case StencilHole::ALT_PTR:
        case StencilHole::ALT_PTR_PUSH: {
          // Patch with the CodeOp* pointer
          // jmpAlt sites are emitted in INITIAL form (movabs head intact) and
          // bind themselves to a direct jmp rel32 on first execution via the
          // bind stub; pushAlt dereferences _mcode at push time.
          uintptr_t altVal = reinterpret_cast<uintptr_t>(op.alternative());
          memcpy(target, &altVal, 8);
          if (altVal) g_jitStats.altNonNull++; else g_jitStats.altNull++;
          // Record for future binary patching
          if (altPatchIdx < 4) {
            op._altPatchOfs[altPatchIdx++] = hole.offset;
          }
          break;
        }

        case StencilHole::FUNCTOR_IMM32: {
          uint32_t functor = static_cast<uint32_t>(op._arg());
          memcpy(target, &functor, 4);
          break;
        }

        case StencilHole::BLOCK_LEN_IMM32: {
          //  The block-head counter's immediate. Only the head variant carries
          //  this hole, so it is reached exactly when i == 0, and nOps is this
          //  block's length - the quantity one add per entry accumulates.
          uint32_t len = static_cast<uint32_t>(nOps);
          memcpy(target, &len, 4);
          break;
        }

        case StencilHole::VAR_BYTE_OFS: {
          uint32_t byteOfs = static_cast<uint32_t>(op._arg() * sizeof(TermList));
          memcpy(target, &byteOfs, 4);
          break;
        }

        case StencilHole::GROUND_TERM_PTR: {
          uintptr_t termPtr = reinterpret_cast<uintptr_t>(op.getTargetTerm());
          memcpy(target, &termPtr, 8);
          break;
        }

        case StencilHole::OP_IMM_PTR: {
          uintptr_t opPtr = reinterpret_cast<uintptr_t>(&op);
          memcpy(target, &opPtr, 8);
          break;
        }

        case StencilHole::NEXT_REL32: {
          // This is a non-trailing NEXT_REL32 (middle of stencil)
          uintptr_t ipAfterJmp = reinterpret_cast<uintptr_t>(target) + 4;
          uintptr_t destAddr;
          if (isLast) {
            destAddr = reinterpret_cast<uintptr_t>(buf + totalSize - BT_STUB_SIZE);
          } else {
            destAddr = reinterpret_cast<uintptr_t>(buf + cursor + copySize);
          }
          int32_t rel = static_cast<int32_t>(destAddr - ipAfterJmp);
          memcpy(target, &rel, 4);
          break;
        }
      }
    }

    cursor += copySize;
  }

  // --- Phase 4: emit the backtrack stub ---
  // jmp [rbp + offsetof(JitExecContext, backtrackHandler)]
  // Encoding: FF /4 mod=10 rm=101(rbp) -> FF A5 <disp32>
  {
    uint8_t* stub = buf + totalSize - BT_STUB_SIZE;
    stub[0] = 0xFF;
    stub[1] = 0xA5;  // ModRM: mod=10, reg=100(/4), rm=101(rbp)
    uint32_t disp = static_cast<uint32_t>(offsetof(JitExecContext, backtrackHandler));
    memcpy(stub + 2, &disp, 4);
  }
  perfMapAdd(buf, totalSize, "cb_%p_g%lu_n%zu", (void*)block, ++g_emitGen, nOps);

  flushICache(buf, totalSize);
}



//  SEARCH STRUCT EMISSION - data-driven design
//
//  The old design asmjit-compiled the binary search INTO instructions:
//  O(N) code regenerated on every SS mutation, which cannot survive
//  saturation-time insert/remove traffic. Now the search runs over the
//  SearchStruct's values[]/targets[] vectors as plain data (ssLookupHelper),
//  reached through one shared, permanently-hot dispatch stub. The only
//  per-SS code is this 16-byte landing stub, emitted exactly once for the
//  SS's lifetime:
//
//     movabs rdi, <&ss->landingOp>    ; 48 BF imm64  (stable address)
//     jmp    [rbp + ssDispatchStub]   ; FF A5 disp32
//
//  Insertions and removals mutate the vectors only: no re-emission, no SMC.
//  Because landing stubs are immutable for the SS lifetime, jmpAlt sites may
//  back-patch (bind) to them like to any block (see bindJmpAltHelper).

void CopyPatchJit::emitSearchStruct(CodeTree::SearchStruct* ss) {
  ASS(_initialized);
  if (ss->landingOp._mcode) return;   // one-time; mutation needs no re-emission

  static constexpr size_t LANDING_STUB_SIZE = 16;
  uint8_t* dest = static_cast<uint8_t*>(allocExec(LANDING_STUB_SIZE));
  dest[0] = 0x48; dest[1] = 0xBF;                        // movabs rdi, imm64
  uintptr_t lp = reinterpret_cast<uintptr_t>(&ss->landingOp);
  memcpy(dest + 2, &lp, 8);
  //  Jump to the shared dispatch stub DIRECTLY where it is in range: 5 bytes
  //  instead of 6, and resolved at decode rather than through a memory operand.
  bool direct = false;
  if (_ssDispatchStub && !std::getenv("JIT_NO_SS_DIRECT")) {
    int64_t rel = static_cast<int64_t>(reinterpret_cast<uintptr_t>(_ssDispatchStub))
                - static_cast<int64_t>(reinterpret_cast<uintptr_t>(dest) + 15);
    if (rel >= INT32_MIN && rel <= INT32_MAX) {
      int32_t r32 = static_cast<int32_t>(rel);
      dest[10] = 0xE9;                                   // jmp rel32
      memcpy(dest + 11, &r32, 4);
      dest[15] = 0x90;                                   // pad to 16
      direct = true;
    }
  }
  if (!direct) {
    dest[10] = 0xFF; dest[11] = 0xA5;                    // jmp [rbp + disp32]
    uint32_t disp = static_cast<uint32_t>(offsetof(JitExecContext, ssDispatchStub));
    memcpy(dest + 12, &disp, 4);
  }
  flushICache(dest, LANDING_STUB_SIZE);
  ss->landingOp._mcode = dest;
  perfMapAdd(dest, LANDING_STUB_SIZE, "ss_%p_n%zu", (void*)ss, ss->length());
  g_jitStats.ssEmits++; g_jitStats.ssBytes += LANDING_STUB_SIZE;
  if (direct) g_jitStats.ssDirectStubs++; else g_jitStats.ssIndirectStubs++;
}


/*
 * emitOutOfLineOp - a standalone FULL-variant copy of one op.
 *
 * Needed because an op emitted from the no-alt stencil variant has no ALT hole
 * to patch when an alternative appears later. Instead of re-emitting the whole
 * block (which would need an interior-op-to-block lookup that does not exist,
 * and would invalidate live code) the op's first five bytes become a jmp to a
 * fresh full-size copy, and the copy transfers to the original op's successor.
 *
 * Three differences from the per-op path in emitBlock:
 *   - always the alt=1 variant, since the whole point is that an alternative
 *     now exists;
 *   - NO trailing-jmp elision: nothing is laid out after this copy;
 *   - every NEXT_REL32 hole, the trailing one included, targets `successor`.
 *
 * Rewrites op._altPatchOfs, but only ONCE EVERY HOLE IS FILLED, so later
 * changes to this op's alternative patch the copy through the ordinary path and
 * a failure part-way leaves the op exactly as it was. Does NOT touch
 * op._mcode: the caller repoints that only once the jmp has actually been
 * written.
 *
 * Bytes land in oolBytes, deliberately NOT in emitBytes, so that the
 * by-kind accounting identity (sum of bytes_* == emit_bytes - 6 per block)
 * stays exact.
 */
uint8_t* CopyPatchJit::emitOutOfLineOp(CodeTree::CodeOp& op, uint8_t* successor)
{
  unsigned instr = op._instruction();
  if (instr == CodeTree::SEARCH_STRUCT) return nullptr;
  //  [1][0]: the full (hasAlt) NON-head variant. An out-of-line copy is
  //  reached by an E9 written over the original op's first five bytes, which on
  //  a head op overwrites the block-entry counter anyway, so the copy must not
  //  carry one - it would have no BLOCK_LEN_IMM32 patch here and would corrupt
  //  the count. The lost counting is bounded by alt_first_appear.
  const Stencil& st = _stencils[1][0][instr];
  if (st.code.empty()) return nullptr;

  const size_t copySize = st.code.size();
  uint8_t* dest = static_cast<uint8_t*>(allocExec(copySize));
  if (!dest) return nullptr;
  memcpy(dest, st.code.data(), copySize);

  //  op._altPatchOfs is NOT touched until the hole loop has succeeded.
  //
  //  The NEXT_REL32 case below can still fail after some holes are filled. An
  //  earlier version overwrote the four slots up front, so a failure there left
  //  the op with ALT_NOALT_TAG gone and hole offsets describing a copy that was
  //  then abandoned, while _mcode still pointed into the block. The next
  //  patchAlternative would take the ordinary branch and try to write eight
  //  bytes at block_base + copy_offset - caught by the site-byte check at the
  //  bottom of patchAlternative only when the bytes there happen not to look
  //  like 48 B8 / 48 B9 / E9.
  //
  //  Staging them means every failure return leaves the op exactly as it was:
  //  still tagged, still described by its in-block code, and the caller's
  //  ool_failed / ool_unreachable tripwire is the only consequence.
  uint16_t staged[4] = { CodeTree::CodeOp::ALT_PATCH_NONE,
                         CodeTree::CodeOp::ALT_PATCH_NONE,
                         CodeTree::CodeOp::ALT_PATCH_NONE,
                         CodeTree::CodeOp::ALT_PATCH_NONE };

  int altPatchIdx = 0;
  for (const auto& hole : st.holes) {
    uint8_t* target = dest + hole.offset;

    switch (hole.kind) {
      case StencilHole::ALT_PTR:
      case StencilHole::ALT_PTR_PUSH: {
        uintptr_t altVal = reinterpret_cast<uintptr_t>(op.alternative());
        memcpy(target, &altVal, 8);
        if (altVal) g_jitStats.altNonNull++; else g_jitStats.altNull++;
        if (altPatchIdx < 4) {
          staged[altPatchIdx++] = hole.offset;
        }
        break;
      }

      case StencilHole::FUNCTOR_IMM32: {
        uint32_t functor = static_cast<uint32_t>(op._arg());
        memcpy(target, &functor, 4);
        break;
      }

      case StencilHole::VAR_BYTE_OFS: {
        uint32_t byteOfs = static_cast<uint32_t>(op._arg() * sizeof(TermList));
        memcpy(target, &byteOfs, 4);
        break;
      }

      case StencilHole::GROUND_TERM_PTR: {
        uintptr_t termPtr = reinterpret_cast<uintptr_t>(op.getTargetTerm());
        memcpy(target, &termPtr, 8);
        break;
      }

      case StencilHole::OP_IMM_PTR: {
        uintptr_t opPtr = reinterpret_cast<uintptr_t>(&op);
        memcpy(target, &opPtr, 8);
        break;
      }

      case StencilHole::BLOCK_LEN_IMM32: {
        //  Unreachable here by construction: this function copies
        //  _stencils[1][0][instr], the NON-head variant, and only the head
        //  variant carries this hole
        //  Patched to 0 rather than left alone, because an unpatched immediate
        //  keeps PH_BLOCKLEN (0xCC000001) and would add 3.4 billion to
        //  blockOps on every entry
        ASS(false);
        uint32_t zero = 0;
        memcpy(target, &zero, 4);
        break;
      }

      case StencilHole::NEXT_REL32: {
        int64_t ipAfterJmp = static_cast<int64_t>(reinterpret_cast<uintptr_t>(target) + 4);
        int64_t rel = static_cast<int64_t>(reinterpret_cast<uintptr_t>(successor)) - ipAfterJmp;
        if (rel < INT32_MIN || rel > INT32_MAX) {
          g_jitStats.oolUnreachable++;
          //  Nothing points at the copy yet - op._altPatchOfs is staged and
          //  _mcode is untouched - so hand the space straight back rather than
          //  leaking it on a path that is already pathological.
          freeExec(dest);
          return nullptr;
        }
        int32_t r = static_cast<int32_t>(rel);
        memcpy(target, &r, 4);
        break;
      }
    }
  }

  //  Commit. From here the op is described by the copy, so later changes to its
  //  alternative patch the copy through the ordinary immediate-rewrite path.
  for (int j = 0; j < 4; j++) { op._altPatchOfs[j] = staged[j]; }

  //  Counted here rather than at the memcpy above so ool_bytes means bytes of
  //  LIVE out-of-line code. The difference is only visible on the failure
  //  return above, which is a tripwire that must stay 0.
  g_jitStats.oolBytes += copySize;

  return dest;
}

/*
 * patchAlternative - called whenever op->_alternative changes on an op that
 * has compiled code. Two jobs:
 *
 *   1. For jmpAlt sites: restore the INITIAL head (movabs rax = 48 B8),
 *      undoing any bound 'jmp rel32' - the unbind side of the PLT protocol.
 *   2. For every ALT hole: overwrite the 8-byte CodeOp* immediate.
 *
 * The hole kind is recovered from the SITE'S OWN BYTES at ofs-2, which are
 * fully determined by our own writers and nothing else:
 *     48 B8  movabs rax  -> jmpAlt site, initial form
 *     E9 ..  jmp rel32   -> jmpAlt site, bound form (unbind first)
 *     48 B9  movabs rcx  -> pushAlt site (immediate rewrite only)
 * Anything else means the site is not what we think it is: refuse to touch
 * it and count patch_badsite (must stay 0).
 */
void CopyPatchJit::patchAlternative(CodeTree::CodeOp* op) {
  if (!op->_mcode) return;
  if (op->isSearchStruct()) return;
  g_jitStats.patchAltCalls++;
  uintptr_t alt = reinterpret_cast<uintptr_t>(op->alternative());
  auto base = static_cast<uint8_t*>(op->_mcode);

  //  NO-ALT FORM. This op has no ALT hole, because it was emitted from the
  //  variant that omits the whole pushAlt/jmpAlt apparatus. Replace its first
  //  five bytes with a jmp to a full-size out-of-line copy, which runs the real
  //  alt logic and then transfers to this op's successor.
  //
  //  Safe because no stencil branches into its own first 25 bytes (verified on
  //  all six alt=0 variants), so the five bytes being overwritten are never a
  //  jump target. The three mangled bytes of whatever immediate started the op
  //  are unreachable the moment byte 0 becomes a jump, and the only non-ALT
  //  holes in the system are write-once at emission.
  //
  //  Assumes index mutation never interleaves with matching: nothing may be
  //  executing inside this op while its head is rewritten. The backtrack stack
  //  holds CodeOp* rather than _mcode (see emitPushAlt) so no stale code
  //  address is parked anywhere, but this is the assumption the scheme rests on.
  if (op->_altPatchOfs[0] == ALT_NOALT_TAG) {
    if (!alt) return;                       // still null: nothing to do
    g_jitStats.altFirstAppear++;

    uint8_t* successor = base + op->_altPatchOfs[3];
    uint8_t* copy = emitOutOfLineOp(*op, successor);
    if (!copy) {
      //  UNSOUND if this ever fires: the alternative is unreachable from
      //  compiled code and the match set is incomplete. Must stay 0.
      g_jitStats.oolFailed++;
      return;
    }

    int64_t rel = static_cast<int64_t>(reinterpret_cast<uintptr_t>(copy))
                - static_cast<int64_t>(reinterpret_cast<uintptr_t>(base) + 5);
    if (rel < INT32_MIN || rel > INT32_MAX) {
      //  Also unsound: entries via _mcode reach the copy but fall-through from
      //  the previous op in the block does not. Must stay 0.
      g_jitStats.oolUnreachable++;
      op->_mcode = copy;
      return;
    }

    int32_t r32 = static_cast<int32_t>(rel);
    base[0] = 0xE9;
    memcpy(base + 1, &r32, 4);
    op->_mcode = copy;
    g_jitStats.oolPatches++;
    return;
  }

  //  Residual safety net: a non-null alternative on an op that is neither
  //  tagged nor carries a hole would be silently lost. Must stay 0.
  {
    bool hasHole = false;
    for (int j = 0; j < 4; j++) {
      if (op->_altPatchOfs[j] != CodeTree::CodeOp::ALT_PATCH_NONE) { hasHole = true; break; }
    }
    if (alt && !hasHole) { g_jitStats.altLostPatch++; return; }
  }

  for (int j = 0; j < 4; j++) {
    auto ofs = op->_altPatchOfs[j];
    if (ofs == CodeTree::CodeOp::ALT_PATCH_NONE) continue;
    uint8_t* head = base + ofs - 2;
    if (head[0] == 0xE9) { g_jitStats.unbinds++; head[0] = 0x48; head[1] = 0xB8; }
    else if (head[0] == 0x48 && (head[1] == 0xB8 || head[1] == 0xB9)) { /* initial form */ }
    else { g_jitStats.patchBadSite++; continue; }
    memcpy(base + ofs, &alt, sizeof(uintptr_t));
    g_jitStats.patchAltStores++;
  }
}


} // namespace Indexing