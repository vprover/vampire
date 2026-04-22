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
static void* mapExecPages(size_t size) {
#ifdef __linux__
  void* p = mmap(nullptr, size, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  return (p == MAP_FAILED) ? nullptr : p;
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

void CopyPatchJit::ensureSlabSpace(size_t size) {
  if (_slabs.empty() || _slabs.back().used + size > _slabs.back().capacity) {
    size_t cap = std::max(SLAB_SIZE, size);
    void* p = mapExecPages(cap);
    ASS(p);
    _slabs.push_back({p, cap, 0});
  }
}

void* CopyPatchJit::slabAlloc(size_t size) {
  // Align to 16 bytes for instruction cache efficiency
  size = (size + 15) & ~15UL;
  ensureSlabSpace(size);
  ExecSlab& slab = _slabs.back();
  void* ptr = static_cast<char*>(slab.base) + slab.used;
  slab.used += size;
  return ptr;
}

void* CopyPatchJit::allocExec(size_t size) {
  return slabAlloc(size);
}

void CopyPatchJit::freeExec(void* /*ptr*/, size_t /*size*/) {
  // Slab allocator doesn't support individual frees.
  // Memory is reclaimed when releaseAll() is called.
}

CopyPatchJit::CopyPatchJit() = default;

CopyPatchJit::~CopyPatchJit() {
  releaseAll();
}

void CopyPatchJit::releaseAll() {
  for (auto& slab : _slabs) {
    unmapExecPages(slab.base, slab.capacity);
  }
  _slabs.clear();
  if (_trampolineBase) {
    sharedRuntime().release(_trampolineBase);
    _trampolineBase = nullptr;
  }
  _trampoline = nullptr;
  _backtrackHandler = nullptr;
  _successHandler = nullptr;
  _totalFailHandler = nullptr;
  _expandStub = nullptr;
  _initialized = false;
}



//  ONE-TIME INITIALIZATION
void CopyPatchJit::initialize() {
  if (_initialized) return;

  compileTrampoline();
  compileExpandStub();

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
}

void CopyPatchJit::compileExpandStub() {
  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  // On entry: rsp is 8 mod 16 (from caller's 'call')
  // push rcx makes rsp 0 mod 16-correct alignment for inner call
  a.push(rcx);                                                       // stack: 0 mod 16

  // store btCursor into ctx so C helper can see it
  a.mov(qword_ptr(rbp, offsetof(JitExecContext, btCursor)), r15);

  // call expandBtBufferHelper(ctx)
  a.mov(rdi, rbp);
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandBtFunc)));    // stack: 0 mod 16

  a.pop(rcx);                                                        // restore mcode

  // reload r15, rbx-buffer may have been reallocated
  a.mov(r15, qword_ptr(rbp, offsetof(JitExecContext, btCursor)));
  a.mov(rbx, qword_ptr(rbp, offsetof(JitExecContext, btEnd)));

  a.ret();

  // Extract into executable memory
  auto bytes = extractCode(code);
  void* dest = allocExec(bytes.size());
  memcpy(dest, bytes.data(), bytes.size());
  flushICache(dest, bytes.size());
  _expandStub = dest;
}

/*
 * Emits:
 *   movabs rcx, <CodeOp* alt>   ; 10 bytes-patchable
 *   test   rcx, rcx
 *   jz     .noPush
 *   mov    rcx, [rcx + _mcode]  ; dereference to mcode
 *   test   rcx, rcx
 *   jz     .noPush
 *   cmp    r15, rbx             ; btCursor >= btEnd?
 *   jb     .doPush
 *   call   [rbp + expandStub]   ; cold: expand buffer, reload r15/rbx
 *   .doPush:
 *   mov    [r15+0], r13         ; tp
 *   mov    [r15+8], rcx         ; alt mcode
 *   add    r15, 16
 *   .noPush:
 *
 * Clobbers: rax, rcx
 */
void CopyPatchJit::emitPushAlt(void* asm_ptr, Stencil& s, size_t base) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

  size_t immOfs = emitMovAbsRcx(a, PH_ALT2) - base;
  s.holes.push_back({StencilHole::ALT_PTR_PUSH, static_cast<uint16_t>(immOfs)});
  s.altHoleCount++;

  Label noPush  = a.new_label();
  Label doPush  = a.new_label();

  a.test(rcx, rcx);
  a.jz(noPush);

  // Dereference CodeOp* -> _mcode
  // The bt stack stores mcode directly so the trampoline backtrack loop can jump without a dependent load.
  a.mov(rcx, qword_ptr(rcx, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rcx, rcx);
  a.jz(noPush);

  a.cmp(r15, rbx);
  a.jb(doPush);

  // call shared expand stub (attempt 3)
  // The stub preserves rcx, reloads r15/rbx, and returns here
  a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));

  a.bind(doPush);
  a.mov(qword_ptr(r15, 0), r13);     // tp
  a.mov(qword_ptr(r15, 8), rcx);     // alt mcode
  a.add(r15, 16);

  a.bind(noPush);
}

/*
 * Emits:
 *   movabs rax, <CodeOp* alt>   ; 10 bytes-patchable CodeOp ptr
 *   test   rax, rax
 *   jz     .bt
 *   mov    rax, [rax + _mcode]
 *   test   rax, rax
 *   jz     .bt
 *   jmp    rax
 *   .bt:
 *   jmp    [rbp+backtrackHandler]
 *
 * Clobbers: rax
 */
void CopyPatchJit::emitJmpAlt(void* asm_ptr, Stencil& s, size_t base) {
  auto& a = *static_cast<Assembler*>(asm_ptr);

  size_t immOfs = emitMovAbsRax(a, PH_ALT1) - base;
  s.holes.push_back({StencilHole::ALT_PTR, static_cast<uint16_t>(immOfs)});
  s.altHoleCount++;

  Label bt = a.new_label();
  a.test(rax, rax);
  a.jz(bt);
  a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jz(bt);
  a.jmp(rax);
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
          // jmpAlt dereferences _mcode at runtime
          // pushAlt dereferences at push time and stores mcode in the backtrack stack
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

  flushICache(buf, totalSize);
}



//  SEARCH STRUCT EMISSION
//
//  SearchStructs are compiled individually with asmjit (not via stencils)
//  because their binary search structure is data-dependent
//  (thought process is that because they change  infrequently compared to CodeBlocks, they dont need a stencil, but im not so sure)
// TODO: reconsider searchstructs in machine code


void CopyPatchJit::emitSearchStruct(CodeTree::SearchStruct* ss) {
  ASS(_initialized);

  auto& rt = sharedRuntime();
  CodeHolder code;
  code.init(rt.environment(), rt.cpu_features());
  Assembler a(&code);

  Label entry = a.new_label();
  a.bind(entry);

  // Load the key value from the flat term
  if (ss->kind == CodeTree::SearchStruct::FN_STRUCT) {
    // key = ft[tp]._number()  =  (content >> 3) & 0x1FFFFFFF
    a.mov(rax, qword_ptr(r12, r13, 3));
    a.shr(rax, 3);
    a.and_(eax, 0x1FFFFFFFu);
  } else {
    // key = ft[tp+1]._term()  =  content & ~7
    a.mov(rax, qword_ptr(r12, r13, 3, 8));
    a.and_(rax, ~7ULL);
  }

  // Shared not-found label
  Label notFoundL = a.new_label();

  uintptr_t landingOpAddr = reinterpret_cast<uintptr_t>(&ss->landingOp);

  // Emit binary search over values[]/targets[]
  auto emitBS = [&](auto& self, size_t lo, size_t hi) -> void {
    if (lo >= hi) {
      a.jmp(notFoundL);
      return;
    }

    size_t mid = lo + (hi - lo) / 2;

    uintptr_t midVal;
    if (ss->kind == CodeTree::SearchStruct::FN_STRUCT) {
      midVal = static_cast<const CodeTree::FnSearchStruct*>(ss)->values[mid];
    } else {
      midVal = reinterpret_cast<uintptr_t>(
        static_cast<const CodeTree::GroundTermSearchStruct*>(ss)->values[mid]);
    }

    emitMovAbsRdx(a, midVal);
    Label lt = a.new_label(), gt = a.new_label();
    a.cmp(rax, rdx);
    a.jl(lt);
    a.jg(gt);

    // Equal-> found the target
    CodeTree::CodeOp* target = ss->targets[mid];
    if (target && target->_mcode) {
      // Push backtrack to landingOp's alternative (if any)
      // Embed CodeOp* (stable), dereference _mcode for bt stack.
      Label noPush = a.new_label();
      Label doPush = a.new_label();

      emitMovAbsRcx(a, landingOpAddr);
      a.mov(rcx, qword_ptr(rcx, offsetof(CodeTree::CodeOp, _alternative)));
      a.test(rcx, rcx);
      a.jz(noPush);
      a.mov(rcx, qword_ptr(rcx, offsetof(CodeTree::CodeOp, _mcode)));
      a.test(rcx, rcx);
      a.jz(noPush);
      a.cmp(r15, rbx);
      a.jb(doPush);
      // Cold-> call shared expand stub
      a.call(qword_ptr(rbp, offsetof(JitExecContext, expandStub)));
      a.bind(doPush);
      a.mov(qword_ptr(r15, 0), r13);
      a.mov(qword_ptr(r15, 8), rcx);
      a.add(r15, 16);
      a.bind(noPush);

      // Jump to target's _mcode (via CodeOp* dereference)
      emitMovAbsRax(a, reinterpret_cast<uintptr_t>(target));
      a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
      a.test(rax, rax);
      a.jz(notFoundL);
      a.jmp(rax);
    } else {
      a.jmp(notFoundL);
    }

    a.bind(lt);
    self(self, lo, mid);
    a.bind(gt);
    self(self, mid + 1, hi);
  };

  emitBS(emitBS, 0, ss->length());

  // Not-found: try landingOp's alternative, then backtrack
  a.bind(notFoundL);
  emitMovAbsRax(a, landingOpAddr);
  a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _alternative)));
  a.test(rax, rax);
  Label noAlt = a.new_label();
  a.jz(noAlt);
  a.mov(rax, qword_ptr(rax, offsetof(CodeTree::CodeOp, _mcode)));
  a.test(rax, rax);
  a.jz(noAlt);
  a.jmp(rax);
  a.bind(noAlt);
  a.jmp(qword_ptr(rbp, offsetof(JitExecContext, backtrackHandler)));

  // Extract and install
  auto bytes = extractCode(code);
  size_t sz = bytes.size();
  void* dest = allocExec(sz);
  memcpy(dest, bytes.data(), sz);
  flushICache(dest, sz);
  ss->landingOp._mcode = static_cast<char*>(dest) + code.label_offset(entry);
}


//  When an alternative changes, overwrite the 8-byte immediates embedded
//  in the movabs instructions.  No recompilation needed.
//
//  On x86-64 the icache is coherent with the dcache, so no flush.

void CopyPatchJit::patchAlternative(CodeTree::CodeOp* op) {
  if (!op->_mcode) return;
  // Embed the CodeOp* pointer (not _mcode)-this is a stable address
  // that survives SearchStruct re-emission.  The stencil code dereferences
  // _mcode at runtime (jmpAlt) or at push time (pushAlt -> bt stack).
  uintptr_t alt = reinterpret_cast<uintptr_t>(op->alternative());
  auto base = static_cast<char*>(op->_mcode);
  for (int j = 0; j < 4; j++) {
    if (op->_altPatchOfs[j] != CodeTree::CodeOp::ALT_PATCH_NONE) {
      memcpy(base + op->_altPatchOfs[j], &alt, sizeof(uintptr_t));
    }
  }
}


} // namespace Indexing