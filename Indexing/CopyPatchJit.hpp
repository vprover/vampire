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
 * @file CopyPatchJit.hpp
 * Copy-and-patch JIT compiler for CodeTree matching.
 */

#ifndef __CopyPatchJit__
#define __CopyPatchJit__

#include <cstdint>
#include <cstddef>
#include <vector>

#include "Forwards.hpp"
#include "Kernel/FlatTerm.hpp"
#include "Kernel/Term.hpp"
#include "CodeTree.hpp"

namespace Indexing {

//  JitExecContext: the register-file bridge between C++ and JIT code
//  Hot fields are at small rbp-relative offsets
struct JitExecContext {
  FlatTerm::Entry* ftData;     // [rbp +  0]  -> r12
  size_t           tp;         // [rbp +  8]  -> r13
  TermList*        bindings;   // [rbp + 16]  -> r14
  void*            btCursor;   // [rbp + 24]  -> r15  (in/out)
  void*            btEnd;      // [rbp + 32]  -> rbx
  void*            btBase;     // [rbp + 40]  (underflow check)
  size_t           curLInfo;   // [rbp + 48]  (loaded on demand)
  void*            op;         // [rbp + 56]  (CodeOp*-in/out)
  uint8_t          matched;    // [rbp + 64]  (out: 1=match, 0=fail)
  uint8_t          _pad[7];    // alignment

  // Handler addresses-loaded by the trampoline, used by stencils
  // via jmp qword ptr [rbp + offset]
  void*            backtrackHandler;  // [rbp + 72]
  void*            successHandler;    // [rbp + 80]
  void*            expandBtFunc;      // [rbp + 88]
  void*            expandStub;        // [rbp + 96] (JIT expand stub-called from pushAlt)

  // Literal iteration fields-used by totalFail handler
  void*            linfos;            // [rbp + 104] (LitInfo* array)
  size_t           linfoCnt;          // [rbp + 112] (number of LitInfos)
  void*            entryMcode;        // [rbp + 120] (entry point _mcode-tree root)
  void*            expandEntryFunc;   // [rbp + 128] (C helper: expand FUN_UNEXPANDED)
  void*            lazyCompileFunc;   // [rbp + 136] (C helper: lazy-compile uncompiled blocks)
  void*            codeTree;          // [rbp + 144] (CodeTree* for lazy compilation callbacks)
  void*            lazyCompileStub;   // [rbp + 152] (JIT stub that calls lazyCompileFunc)

  // PLT-style binding of jmpAlt sites
  void*            bindJmpAltFunc;    // [rbp + 160] (C helper: resolve target + patch site to jmp rel32)
  void*            bindJmpAltStub;    // [rbp + 168] (JIT stub called from initial-form jmpAlt sites)
  size_t           btPops;            // [rbp + 176] (out: backtrack pops during this invocation)

  // Data-driven SearchStruct dispatch
  void*            ssLookupFunc;      // [rbp + 184] (C helper: binary search over ss values[]/targets[])
  void*            ssDispatchStub;    // [rbp + 192] (shared JIT stub entered from 16-byte SS landing stubs)
};

static_assert(offsetof(JitExecContext, ftData)           ==  0, "");
static_assert(offsetof(JitExecContext, tp)               ==  8, "");
static_assert(offsetof(JitExecContext, bindings)         == 16, "");
static_assert(offsetof(JitExecContext, btCursor)         == 24, "");
static_assert(offsetof(JitExecContext, btEnd)            == 32, "");
static_assert(offsetof(JitExecContext, btBase)           == 40, "");
static_assert(offsetof(JitExecContext, curLInfo)         == 48, "");
static_assert(offsetof(JitExecContext, op)               == 56, "");
static_assert(offsetof(JitExecContext, matched)          == 64, "");
static_assert(offsetof(JitExecContext, backtrackHandler) == 72, "");
static_assert(offsetof(JitExecContext, successHandler)   == 80, "");
static_assert(offsetof(JitExecContext, expandBtFunc)     == 88, "");
static_assert(offsetof(JitExecContext, expandStub)       == 96, "");
static_assert(offsetof(JitExecContext, linfos)           == 104, "");
static_assert(offsetof(JitExecContext, linfoCnt)         == 112, "");
static_assert(offsetof(JitExecContext, entryMcode)       == 120, "");
static_assert(offsetof(JitExecContext, expandEntryFunc)  == 128, "");
static_assert(offsetof(JitExecContext, lazyCompileFunc)  == 136, "");
static_assert(offsetof(JitExecContext, codeTree)         == 144, "");
static_assert(offsetof(JitExecContext, lazyCompileStub)  == 152, "");
static_assert(offsetof(JitExecContext, bindJmpAltFunc)   == 160, "");
static_assert(offsetof(JitExecContext, bindJmpAltStub)   == 168, "");
static_assert(offsetof(JitExecContext, btPops)           == 176, "");
static_assert(offsetof(JitExecContext, ssLookupFunc)     == 184, "");
static_assert(offsetof(JitExecContext, ssDispatchStub)   == 192, "");


// --------------------------------------------------------------------------
//  Hole: a patchable location within a compiled stencil.
// --------------------------------------------------------------------------
struct StencilHole {
  enum Kind : uint8_t {
    ALT_PTR,         // 8 bytes: CodeOp* alternative (for jmpAlt; site head is bindable)
    ALT_PTR_PUSH,    // 8 bytes: CodeOp* alternative (for pushAlt)
    FUNCTOR_IMM32,   // 4 bytes: functor/header number
    VAR_BYTE_OFS,    // 4 bytes: var * sizeof(TermList)  (multiple sites)
    GROUND_TERM_PTR, // 8 bytes: Term* for CHECK_GROUND_TERM
    OP_IMM_PTR,      // 8 bytes: CodeOp* for reading _content/writing op
    NEXT_REL32,      // 4 bytes: rel32 jump to next stencil (patched at layout)
  };
  Kind     kind;
  uint16_t offset;  // byte offset within stencil bytes
};

struct Stencil {
  std::vector<uint8_t>    code;
  std::vector<StencilHole> holes;

  // Quick access to the total number of ALT_PTR + ALT_PTR_PUSH holes
  // (needed to set up _altPatchOfs on the CodeOp after emission)
  uint8_t altHoleCount = 0;
};

struct EmittedBlock {
  void*    base    = nullptr;   // start of executable memory
  size_t   size    = 0;         // total bytes
  bool     dirty   = true;      // needs re-emission before next use
};

class CopyPatchJit {
public:
  CopyPatchJit();
  ~CopyPatchJit();
  static void printJitStats(std::ostream& out);
  /** Accumulate the per-invocation backtrack-pop count read back from the
   *  JitExecContext into the global JITSTATS counters. Called from
   *  Matcher::executeMachineCode after the trampoline returns. */
  static void recordBtPops(size_t n);

  // Non-copyable
  CopyPatchJit(const CopyPatchJit&) = delete;
  CopyPatchJit& operator=(const CopyPatchJit&) = delete;

  void initialize();
  void emitBlock(CodeTree::CodeBlock* block);
  void emitSearchStruct(CodeTree::SearchStruct* ss);
  void patchAlternative(CodeTree::CodeOp* op);

  /** Free a JIT allocation previously returned by allocExec.
   *  Called by CodeTree when a block or SearchStruct is removed from the tree.
   */
  void freeCode(void* mcodePtr);

  typedef void (*TrampolineFunc)(JitExecContext*);
  TrampolineFunc trampoline() const { return _trampoline; }

  void* backtrackHandler() const { return _backtrackHandler; }
  void* successHandler()   const { return _successHandler; }

  void initContext(JitExecContext& ctx) const {
    ctx.backtrackHandler = _backtrackHandler;
    ctx.successHandler   = _successHandler;
    ctx.expandBtFunc     = reinterpret_cast<void*>(&expandBtBufferHelper);
    ctx.expandStub       = _expandStub;
    ctx.expandEntryFunc  = reinterpret_cast<void*>(&expandEntryHelper);
    ctx.lazyCompileFunc  = reinterpret_cast<void*>(&lazyCompileHelper);
    ctx.lazyCompileStub  = _lazyCompileStub;
    ctx.bindJmpAltFunc   = reinterpret_cast<void*>(&bindJmpAltHelper);
    ctx.bindJmpAltStub   = _bindJmpAltStub;
    ctx.ssLookupFunc     = reinterpret_cast<void*>(&ssLookupHelper);
    ctx.ssDispatchStub   = _ssDispatchStub;
  }

  void releaseAll();
  bool isInitialized() const { return _initialized; }
  static void expandBtBufferHelper(JitExecContext* ctx);
  static void expandEntryHelper(FlatTerm::Entry* entry);
  static void* lazyCompileHelper(JitExecContext* ctx, CodeTree::CodeOp* alt);
  /** Resolve a jmpAlt dispatch: compile the alternative if needed and, when
   *  safe, patch the calling site into a direct 'jmp rel32' (PLT-style lazy
   *  binding). Returns the target mcode, or nullptr -> stub backtracks. */
  static void* bindJmpAltHelper(JitExecContext* ctx, CodeTree::CodeOp* alt, void* retAddr);
  /** Data-driven SearchStruct lookup: binary search over the (mutable)
   *  values[]/targets[] vectors. Called from the shared ssDispatchStub with
   *  the live register-file values of ftData/tp passed as arguments.
   *  Returns the matching target CodeOp* or nullptr(not found/not a fun). */
  static CodeTree::CodeOp* ssLookupHelper(JitExecContext* ctx, CodeTree::CodeOp* landingOp,
                                          FlatTerm::Entry* ftData, size_t tp);

private:
  void compileTrampoline();
  void compileStencilCheckFun();
  void compileStencilCheckGroundTerm();
  void compileStencilAssignVar();
  void compileStencilCheckVar();
  void compileStencilSuccessOrFail();
  void compileStencilLitEnd();
  void compileExpandStub();
  void compileLazyCompileStub();
  void compileBindJmpAltStub();
  void compileSsDispatchStub();

  void emitPushAlt(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void emitJmpAlt(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void emitNextJump(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void* allocExec(size_t size);
  void  freeExec(void* ptr);

  // TODO revise this strategy, i feel like this is not optimal
  // Segregated free-list allocator for executable memory
  //
  // Each JIT allocation is prepended with a 16-byte header storing the size-class bucket size.
  // On free, the header is read to determine the class and the block is pushed onto a per-class single-linked free list.
  // The next-pointer is stored in the (now-dead) user-data region.

  static constexpr size_t ALLOC_HEADER_SIZE = 16;   // prepended to every alloc

  // Size classes (total bytes including header)
  static constexpr size_t NUM_SIZE_CLASSES = 8;
  static constexpr size_t SIZE_CLASS_SIZES[NUM_SIZE_CLASSES] = {
    64, 128, 256, 512, 1024, 2048, 4096, 8192
  };

  static size_t sizeClassIndex(size_t totalSize);
  static size_t sizeClassBucket(size_t classIdx, size_t totalSize);

  struct FreeNode { FreeNode* next; };
  FreeNode* _freeLists[NUM_SIZE_CLASSES] = {};

  struct ExecSlab {
    void*  base;
    size_t capacity;
    size_t used;
    size_t liveCount;   // number of live (non-freed) allocations in this slab
    bool   inRegion;    // carved from the reserved exec region(not individually unmapped)
  };
  std::vector<ExecSlab> _slabs;
  static constexpr size_t SLAB_SIZE = 4 * 1024 * 1024;  // 4 MB per slab (2 MB-multiple for THP)

  // One large reserved RWX mapping (Linux): all slabs are carved from it so
  // every pair of code addresses is within +-2 GB, guaranteeing that bound
  // 'jmp rel32' sites can always reach their targets. MAP_NORESERVE: untouched
  // pages cost nothing. Non-Linux/mmap-failure falls back to per-slab
  // mappings; the binder then checks reachability per site and simply skips
  // binding when out of range(correct, just unbound).
  static constexpr size_t EXEC_REGION_SIZE = size_t(2) << 30;  // 2 GiB
  char*  _execRegionBase   = nullptr;
  size_t _execRegionSize   = 0;
  size_t _execRegionUsed   = 0;
  bool   _execRegionFailed = false;
  void ensureExecRegion();

  ExecSlab* findSlab(void* ptr);

  void* slabAlloc(size_t size);
  void  ensureSlabSpace(size_t size);

  bool _initialized = false;
  Stencil _stencils[7];

  TrampolineFunc _trampoline = nullptr;

  // Handler addresses within the trampoline
  void* _backtrackHandler  = nullptr;
  void* _successHandler    = nullptr;
  void* _totalFailHandler  = nullptr;

  // Trampoline executable memory
  void* _trampolineBase = nullptr;
  size_t _trampolineSize = 0;

  void* _expandStub = nullptr;
  void* _lazyCompileStub = nullptr;
  void* _bindJmpAltStub = nullptr;
  void* _ssDispatchStub = nullptr;
};

} // namespace Indexing

#endif // __CopyPatchJit__