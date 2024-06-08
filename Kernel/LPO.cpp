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
 * @file LPO.cpp
 * Implements class LPO for instances of the lexicographic path
 * ordering based on Bernd Loechner's thesis "Advances in
 * Equational Theorem Proving - Architecture, Algorithms, and
 * Redundancy Avoidance" Section 4.2
 */



#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "LPO.hpp"
#include "LPOComparator.hpp"
#include "Signature.hpp"

#include <asmjit/a64.h>

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

/**
 * Compare arguments of non-equality literals l1 and l2 and return the
 * result of the comparison.
 */
Ordering::Result LPO::comparePredicates(Literal* l1, Literal *l2) const
{
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if (p1 == p2) {
    ASS_EQ(l1->isNegative(), l1->isNegative()) // this assertion is meaningless. 
    //maybe:  ASS_EQ(l1->isNegative(), l2->isNegative())

    // compare arguments in lexicographic order
    for (unsigned i = 0; i < l1->arity(); i++) {
      Result res = compare(*l1->nthArgument(i), *l2->nthArgument(i));
      if (res != EQUAL)
        return res;
    }
    return EQUAL;
  }

  ASS_NEQ(predicatePrecedence(p1), predicatePrecedence(p2)); // precedence should be total
  return (predicatePrecedence(p1) > predicatePrecedence(p2)) ? GREATER : LESS;
} // LPO::comparePredicates()

Ordering::Result LPO::comparePrecedences(const Term* t1, const Term* t2) const
{
  if (t1->isSort() && t2->isSort()) {
    return compareTypeConPrecedences(t1->functor(), t2->functor());
  }
  // type constuctor symbols are less than function symbols
  if (t1->isSort()) {
    return LESS;
  }
  if (t2->isSort()) {
    return GREATER;
  }
  return compareFunctionPrecedences(t1->functor(), t2->functor());
} // LPO::comparePrecedences

Ordering::Result LPO::compare(TermList tl1, TermList tl2) const
{
  return compare(AppliedTerm(tl1),AppliedTerm(tl2));
}

Ordering::Result LPO::compare(AppliedTerm tl1, AppliedTerm tl2) const
{
  if(tl1.equalsShallow(tl2)) {
    return EQUAL;
  }
  if(tl1.term.isVar()) {
    return tl2.containsVar(tl1.term) ? LESS : INCOMPARABLE;
  }
  ASS(tl1.term.isTerm());
  return clpo(tl1, tl2);
}

bool LPO::isGreater(AppliedTerm lhs, AppliedTerm rhs) const
{
  return lpo(lhs,rhs)==GREATER;
}

Ordering::Result LPO::isGreaterOrEq(AppliedTerm lhs, AppliedTerm rhs) const
{
  return lpo(lhs,rhs);
}

Ordering::Result LPO::clpo(AppliedTerm tl1, AppliedTerm tl2) const
{
  ASS(tl1.term.isTerm());
  if(tl2.term.isVar()) {
    return tl1.containsVar(tl2.term) ? GREATER : INCOMPARABLE;
  }
  ASS(tl2.term.isTerm());
  auto t1=tl1.term.term();
  auto t2=tl2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return cLMA(tl1, tl2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return cMA(tl1, tl2, t2->args(), t2->arity());
  case LESS:
    return Ordering::reverse(cMA(tl2, tl1, t1->args(), t1->arity()));
  default:
    ASSERTION_VIOLATION;
    // shouldn't happen because symbol precedence is assumed to be
    // total, but if it is not then the following call is correct
    //
    // return cAA(t1, t2, t1->args(), t2->args(), t1->arity(), t2->arity());
  }
}

/*
 * All TermList* are stored in reverse order (by design in Term),
 * hence the weird pointer arithmetic
 */
Ordering::Result LPO::cMA(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch(clpo(s, AppliedTerm(*(tl - i),t))) {
    case EQUAL:
    case LESS:
      return LESS;
    case INCOMPARABLE:
      return reverse(alpha(tl - i - 1, arity - i - 1, t, s));
    case GREATER:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

Ordering::Result LPO::cLMA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch(compare(AppliedTerm(*(sl - i),s), AppliedTerm(*(tl - i),t))) {
    case EQUAL:
      break;
    case GREATER:
      return cMA(s, t, tl - i - 1, arity - i - 1);
    case LESS:
      return reverse(cMA(t, s, sl - i - 1, arity - i - 1));
    case INCOMPARABLE:
      return cAA(s, t, sl - i - 1, tl - i - 1, arity - i - 1, arity - i - 1);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

Ordering::Result LPO::cAA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity1, unsigned arity2) const
{
  switch (alpha(sl, arity1, s, t)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return reverse(alpha(tl, arity2, t, s));
  default:
    ASSERTION_VIOLATION;
  }
}

// greater iff some exists s_i in sl such that s_i >= t
Ordering::Result LPO::alpha(const TermList* sl, unsigned arity, AppliedTerm s, AppliedTerm t) const
{
  ASS(t.term.isTerm());
  for (unsigned i = 0; i < arity; i++) {
    if (lpo(AppliedTerm(*(sl - i),s), t) != INCOMPARABLE) {
      return GREATER;
    }
  }
  return INCOMPARABLE;
}

// unidirectional comparison function (returns correct result if tt1 > tt2 or tt1 = tt2)
Ordering::Result LPO::lpo(AppliedTerm tt1, AppliedTerm tt2) const
{
  if(tt1.equalsShallow(tt2)) {
    return EQUAL;
  }
  if (tt1.term.isVar()) {
    return (tt1.term==tt2.term) ? EQUAL : INCOMPARABLE;
  }

  if (tt2.term.isVar()) {
    return tt1.containsVar(tt2.term) ? GREATER : INCOMPARABLE;
  }

  auto t1=tt1.term.term();
  auto t2=tt2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return lexMAE(tt1, tt2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return majo(tt1, tt2, t2->args(), t2->arity());
  default:
    return alpha(t1->args(), t1->arity(), tt1, tt2);
  }
}

Ordering::Result LPO::lexMAE(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(AppliedTerm(*(sl - i),s), AppliedTerm(*(tl - i),t))) {
    case EQUAL:
      break;
    case GREATER:
      return majo(s, t, tl - i - 1, arity - i - 1);
    case INCOMPARABLE:
      return alpha(sl - i - 1, arity - i - 1, s, t);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

// greater if s is greater than every term in tl
Ordering::Result LPO::majo(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    if (lpo(s, AppliedTerm(*(tl - i), t)) != GREATER) {
      return INCOMPARABLE;
    }
  }
  return GREATER;
}

template <class T>
constexpr int VFnOffset(T func)
{
    union
    {
        T ptr;
        int i;
    };
    ptr = func;

    return i;
}

bool LPO::isGreater(TermList lhs, TermList rhs, const SubstApplicator* applicator, OrderingComparatorUP& comparator) const
{
  if (!comparator) {
    // cout << "preprocessing " << lhs << " " << rhs << endl;
    comparator = make_unique<const LPOComparator>(lhs, rhs, *this);
    // cout << comparator->toString() << endl;

    using namespace asmjit;

    static JitRuntime rt;

    auto c = const_cast<LPOComparator*>(static_cast<const LPOComparator*>(comparator.get()));
    // CodeHolder code;
    c->code.init(rt.environment(), rt.cpuFeatures());

    using namespace a64;

    Assembler a(&c->code);

    // prologue

    a.stp(x29,x30,ptr_pre(sp,-96));             // save x29 (frame pointer) and x30 (link register / return address) to stack, also move stack cursor 96 units up
    a.mov(x29,sp);                              // x29 <- sp  (x29 holds frame pointer)
    a.stp(x19,x20,ptr(sp,16));
    a.mov(x20,x0);                              // store 1st arg (const Ordering*) in x20
    a.mov(x19,x1);                              // store 2nd arg (const SubstApplicator*) in x19

    vvector<Label> labels(c->_instructions.size());
    Label endLabel = a.newLabel();

    for (unsigned i = 1; i < c->_instructions.size(); i++) {
      labels[i] = a.newLabel();
    }

    for (unsigned i = 0; i < c->_instructions.size(); i++) {

      if (i > 0) {
        a.bind(labels[i]);
      }

      // (*applicator)(var1.var()) call

      const auto& ins = static_cast<const LPOComparator*>(comparator.get())->_instructions[i];

      if (ins.lhs.isVar()) {
        a.mov(x0,x19);                              // new 1st arg is applicator
        a.mov(x1,ins.lhs.var());                       // new 2nd arg is var1.var()
        a.ldr(x2,ptr(x19));                         // load SubstApplicator vtable ptr into x2
        a.ldr(x2,ptr(x2,                            // load SubstApplicator::operator() ptr into x2
          VFnOffset(&SubstApplicator::operator())));
        a.str(x21,ptr(sp,32));                      // store x21 value on stack+32
        a.blr(x2);                                  // perform call
        a.stp(x0,xzr,ptr(sp, 40));                  // store result of call and false on stack
        a.str(x19,ptr(sp,
          40+offsetof(AppliedTerm,applicator)));    // store appl (3rd arg to AppliedTerm) on stack
      } else {
        a.mov(x0,*reinterpret_cast<const uint64_t*>(&ins.lhs));
        a.mov(x1,1);
        a.stp(x0,x1,ptr(sp, 40));                   // store result of call and true on stack
        a.str(x19,ptr(sp,
          40+offsetof(AppliedTerm,applicator)));    // store appl (3rd arg to AppliedTerm) on stack
      }

      // (*applicator)(var2.var()) call

      if (ins.rhs.isVar()) {
        a.mov(x0,x19);                              // new 1st arg is applicator
        a.mov(x1,ins.rhs.var());                       // new 2nd arg is var2.var()
        a.ldr(x2,ptr(x19));                         // load SubstApplicator vtable ptr into x2
        a.ldr(x2,ptr(x2,                            // load SubstApplicator::operator() ptr into x2
          VFnOffset(&SubstApplicator::operator())));
        a.blr(x2);                                  // perform call
        a.stp(x0,xzr,ptr(sp,64));                   // store result of call and false on stack
        a.str(x19,ptr(sp,
          64+offsetof(AppliedTerm,applicator)));    // store appl (3rd arg to AppliedTerm) on stack
      } else {
        a.mov(x0,*reinterpret_cast<const uint64_t*>(&ins.rhs));
        a.mov(x1,1);
        a.stp(x0,x1,ptr(sp,64));                    // store result of call and true on stack
        a.str(x19,ptr(sp,
          64+offsetof(AppliedTerm,applicator)));    // store appl (3rd arg to AppliedTerm) on stack
      }

      // ord->isGreaterOrEq call
      // TODO replace this with non-virtual LPO::lpo

      a.mov(x0,x20);                              // new 1st arg is ordering
      a.ldr(x3,ptr(x20));                         // load Ordering vtable ptr into x2
      a.ldr(x21,ptr(x3,                           // load Ordering::isGreaterOrEq into x21
        VFnOffset(&Ordering::isGreaterOrEq)));
      a.add(x1,sp,40);                            // 2nd arg, AppliedTerm(var1,false,applicator)
      a.add(x2,sp,64);                            // probably 3rd argument, AppliedTerm(var2,false,applicator)
      a.blr(x21);                                 // perform call
      // a.bl(Imm(&LPO::lpo));

      a.mov(x1,x0);
      // eq branch
      a.cmp(x1,Ordering::EQUAL);
      switch (ins.bs[0].tag) {
        case LPOComparator::Instruction::BranchTag::T_JUMP: {
          a.b_eq(labels[ins.bs[0].jump_pos]);
          break;
        }
        case LPOComparator::Instruction::BranchTag::T_GREATER: {
          a.mov(w0, 1);
          a.b_eq(endLabel);
          break;
        }
        default: {
          a.mov(w0, 0);
          a.b_eq(endLabel);
          break;
        }
      }
      // gt branch
      // a.cmp(x1,Ordering::GREATER);
      switch (ins.bs[1].tag) {
        case LPOComparator::Instruction::BranchTag::T_JUMP: {
          a.b_le(labels[ins.bs[1].jump_pos]);
          break;
        }
        case LPOComparator::Instruction::BranchTag::T_GREATER: {
          a.mov(w0, 1);
          a.b_le(endLabel);
          break;
        }
        default: {
          a.mov(w0, 0);
          a.b_le(endLabel);
          break;
        }
      }
      // incomparable branch
      // a.cmp(x1,Ordering::INCOMPARABLE);
      switch (ins.bs[2].tag) {
        case LPOComparator::Instruction::BranchTag::T_JUMP: {
          a.b(labels[ins.bs[2].jump_pos]);
          break;
        }
        case LPOComparator::Instruction::BranchTag::T_GREATER: {
          a.mov(w0, 1);
          a.b(endLabel);
          break;
        }
        default: {
          a.mov(w0, 0);
          a.b(endLabel);
          break;
        }
      }
    }

    // epilogue

    a.bind(endLabel);

    a.ldr(x21,ptr(sp,32));
    a.ldp(x19,x20,ptr(sp,16));
    a.ldp(x29,x30,ptr_post(sp,96));
    a.ret(x30);  // x30 holds *where* to return

    // Func fn;
    Error err = rt.add(&c->fn, &c->code);

    if (err) {
      printf("AsmJit failed: %s\n", DebugUtils::errorAsString(err));
      USER_ERROR("jit assembling failed");
    }

    // TODO release code
    // rt.release(c->fn);
  }
  auto c = static_cast<const LPOComparator*>(comparator.get());
  // return c->check(applicator);
  return c->fn(this, applicator);
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
