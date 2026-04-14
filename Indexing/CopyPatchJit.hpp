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
  void*            expandStub;        // [rbp + 96]  (JIT expand stub-called from pushAlt)

  // Literal iteration fields-used by totalFail handler
  void*            linfos;            // [rbp + 104] (LitInfo* array)
  size_t           linfoCnt;          // [rbp + 112] (number of LitInfos)
  void*            entryMcode;        // [rbp + 120] (entry point _mcode-tree root)
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


// --------------------------------------------------------------------------
//  Hole: a patchable location within a compiled stencil.
// --------------------------------------------------------------------------
struct StencilHole {
  enum Kind : uint8_t {
    ALT_PTR,         // 8 bytes: CodeOp* alternative (for jmpAlt)
    ALT_PTR_PUSH,    // 8 bytes: CodeOp* alternative (for pushAlt)
    FUNCTOR_IMM32,   // 4 bytes: functor/header number
    VAR_BYTE_OFS,    // 4 bytes: var * sizeof(TermList)  (multiple sites)
    GROUND_TERM_PTR, // 8 bytes: Term* for CHECK_GROUND_TERM
    OP_IMM_PTR,      // 8 bytes: CodeOp* for reading _content / writing op
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

  // Non-copyable
  CopyPatchJit(const CopyPatchJit&) = delete;
  CopyPatchJit& operator=(const CopyPatchJit&) = delete;

  void initialize();
  void emitBlock(CodeTree::CodeBlock* block);
  void emitSearchStruct(CodeTree::SearchStruct* ss);
  void patchAlternative(CodeTree::CodeOp* op);

  typedef void (*TrampolineFunc)(JitExecContext*);
  TrampolineFunc trampoline() const { return _trampoline; }

  void* backtrackHandler() const { return _backtrackHandler; }
  void* successHandler()   const { return _successHandler; }

  void initContext(JitExecContext& ctx) const {
    ctx.backtrackHandler = _backtrackHandler;
    ctx.successHandler   = _successHandler;
    ctx.expandBtFunc     = reinterpret_cast<void*>(&expandBtBufferHelper);
    ctx.expandStub       = _expandStub;
  }

  void releaseAll();
  bool isInitialized() const { return _initialized; }
  static void expandBtBufferHelper(JitExecContext* ctx);

private:
  void compileTrampoline();
  void compileStencilCheckFun();
  void compileStencilCheckGroundTerm();
  void compileStencilAssignVar();
  void compileStencilCheckVar();
  void compileStencilSuccessOrFail();
  void compileStencilLitEnd();
  void compileExpandStub();

  void emitPushAlt(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void emitJmpAlt(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void emitNextJump(void* assembler_ptr, Stencil& s, size_t baseOffset);
  void* allocExec(size_t size);
  void  freeExec(void* ptr, size_t size);

  struct ExecSlab {
    void*  base;
    size_t capacity;
    size_t used;
  };
  std::vector<ExecSlab> _slabs;
  static constexpr size_t SLAB_SIZE = 1024 * 1024;  // 1 MB per slab

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
};

} // namespace Indexing

#endif // __CopyPatchJit__