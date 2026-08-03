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
#include <cstdlib>
#include <algorithm>

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

// Distance from the start of a jmpAlt site (the movabs opcode) to the return
// address pushed by the site's 'call [rbp+bindJmpAltStub]'. All jmpAlt sites
// share one byte-identical layout, so this is measured once during stencil
// compilation (emitJmpAlt) and asserted equal on every subsequent emission.
static size_t s_jmpAltRetOfs = 0;

struct JitStats {
  size_t emitBlocks = 0, emitBytes = 0, emitOps = 0;
  size_t ssEmits = 0, ssBytes = 0;
  size_t ssLookups = 0, ssFound = 0;
  size_t frees = 0;
  size_t patchAltCalls = 0, patchAltStores = 0;
  size_t lazyCompiles = 0;
  size_t slabsMapped = 0, slabBytes = 0;
  // PLT-style binding of jmpAlt sites
  size_t bindCalls = 0;        // trips through the bind stub (once per site per bind epoch)
  size_t binds = 0;            // sites patched to direct 'jmp rel32'
  size_t unbinds = 0;          // bound sites restored to initial form by patchAlternative
  size_t bindUnreachable = 0;  // target outside +-2 GB: left unbound (fallback slabs only)
  size_t bindBadSite = 0;      // site head bytes unexpected: refused to patch (should stay 0)
  size_t patchBadSite = 0;     // patchAlternative met unexpected head bytes: refused (should stay 0)
  size_t execRegionMB = 0;     // size of the reserved exec region actually obtained
  // trampoline instrumentation
  size_t btPops = 0;           // backtrack-stack pops resumed by the bt handler
};

JitStats g_jitStats;
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

void CopyPatchJit::printJitStats(std::ostream& out)
{
  const JitStats& s = g_jitStats;
  if (!s.emitBlocks && !s.ssEmits && !s.slabsMapped) return;  // JIT never ran: stay silent
  out << "% JITSTATS"
      << " emit_blocks=" << s.emitBlocks
      << " emit_bytes=" << s.emitBytes
      << " emit_ops=" << s.emitOps
      << " ss_emits=" << s.ssEmits
      << " ss_bytes=" << s.ssBytes
      << " ss_lookups=" << s.ssLookups
      << " ss_found=" << s.ssFound
      << " frees=" << s.frees
      << " patch_alt_calls=" << s.patchAltCalls
      << " patch_alt_stores=" << s.patchAltStores
      << " lazy_compiles=" << s.lazyCompiles
      << " slabs=" << s.slabsMapped
      << " slab_bytes=" << s.slabBytes
      << " bind_calls=" << s.bindCalls
      << " binds=" << s.binds
      << " unbinds=" << s.unbinds
      << " bind_unreachable=" << s.bindUnreachable
      << " bind_badsite=" << s.bindBadSite
      << " patch_badsite=" << s.patchBadSite
      << " exec_region_mb=" << s.execRegionMB
      << " bt_pops=" << s.btPops
      << std::endl;
}

void CopyPatchJit::recordBtPops(size_t n)
{
  g_jitStats.btPops += n;
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
  g_jitStats.lazyCompiles++;
  auto* tree = static_cast<CodeTree*>(ctx->codeTree);
  return tree->lazyCompileBlock(alt);
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
  void* target = alt->_mcode;
  if (!target) {
    g_jitStats.lazyCompiles++;
    target = tree->lazyCompileBlock(alt);
  }
  if (!target) return nullptr;
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
  g_jitStats.ssLookups++;
  CodeTree::CodeOp* target = landingOp->getSearchStruct()->getTargetOp(ftData + tp);
  if (target) g_jitStats.ssFound++;
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
  madvise(aligned, size, MADV_HUGEPAGE);
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
  if (_execRegionBase || _execRegionFailed) return;
#ifndef __linux__
  _execRegionFailed = true;
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
      _execRegionBase = aligned;
      _execRegionSize = want;
      _execRegionUsed = 0;
      g_jitStats.execRegionMB = want >> 20;
      return;
    }
    want >>= 1;
  }
  _execRegionFailed = true;
#endif
}

void CopyPatchJit::ensureSlabSpace(size_t size) {
  if (!_slabs.empty() && _slabs.back().used + size <= _slabs.back().capacity) return;

  const size_t TWO_MB = size_t(2) << 20;
  size_t cap = std::max(SLAB_SIZE, size);
  cap = (cap + TWO_MB - 1) & ~(TWO_MB - 1);   // THP: whole 2 MiB units

  ensureExecRegion();
  void* p = nullptr;
  bool inRegion = false;
  if (_execRegionBase && _execRegionUsed + cap <= _execRegionSize) {
    p = _execRegionBase + _execRegionUsed;
    _execRegionUsed += cap;
    inRegion = true;
#ifdef __linux__
    madvise(p, cap, MADV_HUGEPAGE);
#endif
  } else {
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
  size_t classIdx  = sizeClassIndex(totalSize);
  size_t bucket    = sizeClassBucket(classIdx, totalSize);

  uint8_t* raw = nullptr;

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
  size_t headerVal = bucket;
  memcpy(raw, &headerVal, sizeof(size_t));

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
    // Region-carved slabs are released with the region below.
    if (!slab.inRegion) {
      unmapExecPages(slab.base, slab.capacity);
    }
  }
  _slabs.clear();
  if (_execRegionBase) {
#ifdef __linux__
    munmap(_execRegionBase, _execRegionSize);
#endif
    _execRegionBase = nullptr;
    _execRegionSize = 0;
    _execRegionUsed = 0;
  }
  _execRegionFailed = false;
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

  compileStencilSuccessOrFail();
  compileStencilCheckGroundTerm();
  compileStencilLitEnd();
  compileStencilCheckFun();
  compileStencilAssignVar();
  compileStencilCheckVar();
  // _stencils[SEARCH_STRUCT] is left empty-SearchStructs are handled
  // differently (they're compiled individually, not via stencils).

  _initialized = true;
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
  // A null ctx.op signals "resume from backtrack stack"-used when
  // re-entering after a yield, avoiding the need for C++ to interpret
  // the JIT backtrack stack (which now stores mcode, not CodeOp*).
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
  // Pop a {tp, mcode*} pair from the backtrack stack and resume.
  a.bind(backtrackL);
  a.cmp(r15, qword_ptr(rbp, offsetof(JitExecContext, btBase)));
  a.je(totalFailL);
  a.sub(r15, 16);
  a.mov(r13, qword_ptr(r15, 0));    // tp
  a.mov(rax, qword_ptr(r15, 8));    // mcode directly
  a.test(rax, rax);
  a.jz(backtrackL);                  // null mcode -> keep backtracking
  // Instrumentation: count resumed pops (splits backtrack-dispatch traffic
  // from jmpAlt-dispatch traffic; ~1 extra instruction per pop, remove the
  // line for pristine timing runs if desired).
  a.inc(qword_ptr(rbp, offsetof(JitExecContext, btPops)));
  a.jmp(rax);

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
 *   found:     push {tp, alt mcode} if landingOp has an alternative,
 *              then jump to target's code (which re-verifies the key itself)
 *   not found: jump to the alternative directly (nothing was pushed), or
 *              backtrack if there is none
 * The interpreter pushes the alternative first and pops it on failure; the
 * two orderings are observationally identical and this one skips the
 * push/pop round trip on the miss path.
 */
void CopyPatchJit::compileSsDispatchStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  Label notFound   = a.new_label();
  Label havePushM  = a.new_label();
  Label doPush     = a.new_label();
  Label dispatch   = a.new_label();
  Label go         = a.new_label();
  Label goAlt      = a.new_label();
  Label bt         = a.new_label();

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
  a.test(rax, rax);
  a.jz(notFound);

  // --- FOUND: rax = target CodeOp* ---
  a.mov(rdx, rax);          // rdx = target (survives lazyCompileStub/expandStub)
  a.mov(rax, qword_ptr(rdi, offsetof(CodeTree::CodeOp, _alternative)));
  a.test(rax, rax);
  a.jz(dispatch);
  // push {tp, alt mcode}, lazy-compiling the alternative if needed
  a.mov(rcx, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rcx, rcx);
  a.jnz(havePushM);
  a.mov(rcx, rax);          // stub convention: rcx = CodeOp*
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.mov(rcx, rax);
  a.test(rcx, rcx);
  a.jz(dispatch);           // uncompilable alternative: skip the push
  a.bind(havePushM);
  a.cmp(r15, rbx);
  a.jb(doPush);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));
  a.bind(doPush);
  a.mov(qword_ptr(r15, 0), r13);
  a.mov(qword_ptr(r15, 8), rcx);
  a.add(r15, 16);
  a.bind(dispatch);
  // jump to target's code (lazy-compile if needed)
  a.mov(rax, qword_ptr(rdx, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jnz(go);
  a.mov(rcx, rdx);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.test(rax, rax);
  a.jz(bt);                 // pushed alt (if any) is popped by backtrack: single visit
  a.bind(go);
  a.jmp(rax);

  // --- NOT FOUND: nothing pushed -> alternative directly, or backtrack ---
  a.bind(notFound);
  a.mov(rax, qword_ptr(rdi, offsetof(CodeTree::CodeOp, _alternative)));
  a.test(rax, rax);
  a.jz(bt);
  a.mov(rcx, rax);          // CodeOp* for the lazy path
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

  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _ssDispatchStub = dest;
  perfMapAdd(dest, bytes.size(), "jit_ss_dispatch_stub");
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
 *   mov    [r15+8], rcx         ; alt mcode
 *   add    r15, 16
 *   .noPush:
 *
 * Hot-path clobbers: rcx, rdi.   rax is UNTOUCHED on hot path.
 * Cold-path clobbers: rax, rcx, rdi, rsi (via call)
 *
 * pushAlt is deliberately NOT bound: it resolves _mcode at push time, and the
 * pushed value lives only within one trampoline invocation, so it stays
 * correct under index mutation without any patching protocol.
 */
void CopyPatchJit::emitPushAlt(void* asm_ptr, Stencil& s, size_t base) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

  size_t immOfs = emitMovAbsRcx(a, PH_ALT2) - base;
  s.holes.push_back({StencilHole::ALT_PTR_PUSH, static_cast<uint16_t>(immOfs)});
  s.altHoleCount++;

  Label noPush = a.new_label();
  Label doPush = a.new_label();
  Label haveMcode = a.new_label();

  a.test(rcx, rcx);
  a.jz(noPush);

  a.mov(rdi, rcx);  // save CodeOp* in rdi (for lazy compile path)
  a.mov(rcx, qword_ptr(rcx, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rcx, rcx);
  a.jnz(haveMcode);

  // Cold path: _mcode is null->call lazy compile stub
  a.mov(rcx, rdi);   // pass CodeOp* in rcx (stub convention)
  a.call(qword_ptr(rbp, offsetof(JitExecContext, lazyCompileStub)));
  a.mov(rcx, rax);   // result->rcx
  a.test(rcx, rcx);
  a.jz(noPush);      // still null->skip

  a.bind(haveMcode);
  a.cmp(r15, rbx);
  a.jb(doPush);

  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));

  a.bind(doPush);
  a.mov(qword_ptr(r15, 0), r13);     // tp
  a.mov(qword_ptr(r15, 8), rcx);     // alt mcode
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
void CopyPatchJit::emitJmpAlt(void* asm_ptr, Stencil& s, size_t base) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

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

void CopyPatchJit::compileStencilCheckFun() {
  Stencil& s = _stencils[CodeTree::CHECK_FUN];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

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
  emitJmpAlt(&a, s, base);

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

  emitPushAlt(&a, s, base);
  a.add(r13, FlatTerm::FUNCTION_ENTRY_COUNT);
  emitNextJump(&a, s, base);

  // Record the functor hole
  s.holes.push_back({StencilHole::FUNCTOR_IMM32, static_cast<uint16_t>(funcOfs)});

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilCheckGroundTerm() {
  Stencil& s = _stencils[CodeTree::CHECK_GROUND_TERM];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

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
  emitJmpAlt(&a, s, base);

  a.bind(matched);
  // Load FUN_RIGHT_OFS: (ft[tp+2]._content >> 3) & 0x1FFFFFFF
  a.mov(r10, qword_ptr(rax, 16));
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);
  emitPushAlt(&a, s, base);
  a.add(r13, r10);
  emitNextJump(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilAssignVar() {
  Stencil& s = _stencils[CodeTree::ASSIGN_VAR];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

  // Load ft[tp]
  a.lea(rax, ptr(r12, r13, 3));
  a.mov(r11, qword_ptr(rax));
  a.mov(rdx, r11);
  a.and_(rdx, 7);
  Label funCase = a.new_label();
  a.cmp(rdx, FlatTerm::VAR);
  a.jne(funCase);

  // ---- Variable case ----
  emitPushAlt(&a, s, base);
  // Construct TermList for var: (number << 2) | 1
  a.mov(rdx, r11);
  a.shr(rdx, 3);
  a.and_(edx, 0x1FFFFFFFu);
  a.shl(rdx, 2);
  a.or_(rdx, 1);

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

  emitPushAlt(&a, s, base);

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

void CopyPatchJit::compileStencilCheckVar() {
  Stencil& s = _stencils[CodeTree::CHECK_VAR];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

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
  emitJmpAlt(&a, s, base);
  a.bind(varMatched);
  emitPushAlt(&a, s, base);
  a.inc(r13);
  emitNextJump(&a, s, base);

  // ---- Function case ----
  a.bind(funCase);
  a.mov(r10, qword_ptr(rax, 8));      // Term*
  Label funMatched = a.new_label();
  a.cmp(r10, rdx);
  a.je(funMatched);
  emitJmpAlt(&a, s, base);
  a.bind(funMatched);
  // Load FUN_RIGHT_OFS into r10 before pushAlt
  a.mov(r10, qword_ptr(rax, 16));
  a.shr(r10, 3);
  a.and_(r10d, 0x1FFFFFFFu);
  emitPushAlt(&a, s, base);
  a.add(r13, r10);
  emitNextJump(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilSuccessOrFail() {
  Stencil& s = _stencils[CodeTree::SUCCESS_OR_FAIL];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

  // Load op._content via op pointer
  size_t opOfs = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfs)});

  a.mov(rdx, qword_ptr(rax, 0));      // rdx = _content
  Label isSuccess = a.new_label();
  a.test(rdx, rdx);
  a.jnz(isSuccess);

  // Fail: jmpAlt
  emitJmpAlt(&a, s, base);

  // Success:
  a.bind(isSuccess);
  // Check curLInfo == 0
  a.mov(rcx, qword_ptr(rbp, offsetof(JitExecContext, curLInfo)));
  Label notFirstRound = a.new_label();
  a.test(rcx, rcx);
  a.jnz(notFirstRound);

  // First round: pushAlt, then yield success
  emitPushAlt(&a, s, base);

  // Store op ptr into ctx
  size_t opOfs2 = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfs2)});
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, op)), rax);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, successHandler)));

  // Not first round? ->backtrack
  a.bind(notFirstRound);
  emitJmpAlt(&a, s, base);

  s.code = extractCode(code);
}

void CopyPatchJit::compileStencilLitEnd() {
  Stencil& s = _stencils[CodeTree::LIT_END];
  CodeHolder code;
  auto& rt = sharedRuntime();
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);
  size_t base = a.offset();

  size_t opOfsChk = emitMovAbsRax(a, PH_OPPTR) - base;
  s.holes.push_back({StencilHole::OP_IMM_PTR, static_cast<uint16_t>(opOfsChk)});
  a.mov(rdx, qword_ptr(rax, 0));
  Label notFail = a.new_label();
  a.test(rdx, rdx);
  a.jnz(notFail);
  emitJmpAlt(&a, s, base);

  a.bind(notFail);

  emitPushAlt(&a, s, base);

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
    const Stencil& st = _stencils[instr];
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

  // --- Phase 3: copy-and-patch each op ---
  for (size_t i = 0; i < nOps; i++) {
    CodeTree::CodeOp& op = (*block)[i];
    unsigned instr = op._instruction();
    const Stencil& st = _stencils[instr];
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

    // Record _mcode
    op._mcode = dest;

    // Reset patch offsets
    for (int j = 0; j < 4; j++) {
      op._altPatchOfs[j] = CodeTree::CodeOp::ALT_PATCH_NONE;
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
  dest[10] = 0xFF; dest[11] = 0xA5;                      // jmp [rbp + disp32]
  uint32_t disp = static_cast<uint32_t>(offsetof(JitExecContext, ssDispatchStub));
  memcpy(dest + 12, &disp, 4);
  flushICache(dest, LANDING_STUB_SIZE);
  ss->landingOp._mcode = dest;
  perfMapAdd(dest, LANDING_STUB_SIZE, "ss_%p_n%zu", (void*)ss, ss->length());
  g_jitStats.ssEmits++; g_jitStats.ssBytes += LANDING_STUB_SIZE;
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
  for (int j = 0; j < 4; j++) {
    auto ofs = op->_altPatchOfs[j];
    if (ofs == CodeTree::CodeOp::ALT_PATCH_NONE) continue;
    uint8_t* head = base + ofs - 2;
    if (head[0] == 0xE9) {
      // bound jmpAlt site: unbind, then rewrite the immediate
      g_jitStats.unbinds++;
      head[0] = 0x48;
      head[1] = 0xB8;
    } else if (head[0] == 0x48 && (head[1] == 0xB8 || head[1] == 0xB9)) {
      // initial jmpAlt (B8) or pushAlt (B9): immediate rewrite only
    } else {
      g_jitStats.patchBadSite++;   // unexpected bytes: never touch them
      continue;
    }
    memcpy(base + ofs, &alt, sizeof(uintptr_t));
    g_jitStats.patchAltStores++;
  }
}


} // namespace Indexing