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
 * @file TestUtils.cpp
 * Implements class TestUtils.
 */

#include <cstdarg>


#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"

#include "TestUtils.hpp"

namespace Test {

using namespace Kernel;
using namespace Shell;

SAT::SATClause* TestUtils::buildSATClause(unsigned len,...)
{
  using namespace SAT;

  va_list litArgs;
  va_start(litArgs,len);

  static SATLiteralStack lits;
  lits.reset();
  for(unsigned i=0; i<len; ++i) {
    int litVal = va_arg(litArgs, int);
    bool pos = litVal>0;
    unsigned var = pos ? litVal : -litVal;
    lits.push(SATLiteral(var, pos));
  }

  va_end(litArgs);

  return SATClause::fromStack(lits);
}

std::ostream& printOp(std::ostream& out, const Term* t, const char* op) {
  auto l = *t->nthArgument(0);
  auto r = *t->nthArgument(1);
  return out << "(" << pretty(l) << " " << op << " " << pretty(r) << ")";
}

template<>
std::ostream& Pretty<Kernel::TermList>::prettyPrint(std::ostream& out) const
{
  using namespace Kernel;

  auto t = _self;
  if (t.isVar()) {
    return out << "X" << t.var();
  } else {
    auto term = t.term();
    auto func = term->functor();
    if (theory->isInterpretedFunction(func)) {
      switch(theory->interpretFunction(func)) {
#define NUM_CASE(oper) \
        case Kernel::Theory::INT_  ## oper: \
        case Kernel::Theory::REAL_ ## oper: \
        case Kernel::Theory::RAT_  ## oper

        NUM_CASE(PLUS):     
          return printOp(out, term, "+");
        NUM_CASE(MULTIPLY):
          return printOp(out, term, "*");
        // case Kernel::Theory::EQUAL:
        //   return printOp("=")
        default: {}
#undef NUM_CASE
      }
    }

    Signature::Symbol* sym = env.signature->getFunction(func);
    out << sym->name();
    if (sym->arity() > 0) {
      out << "(" << pretty(*term->nthArgument(0));
      for (unsigned i = 1; i < sym->arity(); i++) {
        out << ", " << pretty(*term->nthArgument(i));
      }
      out << ")";
    }
    return out;
  }
}

template<>
std::ostream& Pretty<Literal*>::prettyPrint(std::ostream& out) const
{ return out << pretty(*_self); }


template<>
std::ostream& Pretty<Clause>::prettyPrint(std::ostream& out) const
{ 
  auto iter = _self.iterLits();
  if (iter.hasNext()) {
    out << pretty(*iter.next());
    while(iter.hasNext()) {
      out << " \\/ " << pretty(*iter.next());
    }
  } else {
    out << "bot";
  }
  return out;
}

template<>
std::ostream& Pretty<Literal>::prettyPrint(std::ostream& out) const
{
  const Literal& lit = _self;
  auto print = [&]() -> ostream& {

    auto func = lit.functor();
    if(theory->isInterpretedPredicate(func)) {
      switch(theory->interpretPredicate(func)) {
#define NUM_CASE(oper) \
        case Kernel::Theory::INT_  ## oper: \
        case Kernel::Theory::REAL_ ## oper: \
        case Kernel::Theory::RAT_  ## oper

        NUM_CASE(LESS_EQUAL):
          return printOp(out, &lit, "<=");
        case Kernel::Theory::EQUAL:
          return printOp(out, &lit, "=");
        default: 
        {
        }
#undef NUM_CASE
      }
    }
    Signature::Symbol* sym = env.signature->getPredicate(func);
    out << sym->name();
    if (sym->arity() > 0) {
      out << "(" << pretty(*lit.nthArgument(0));
      for (unsigned i = 1; i < sym->arity(); i++) {
        out << ", " << pretty(*lit.nthArgument(i));
      }
      out << ")";
    }
    return out;
  };


  if (!lit.polarity()) {
    out << "~(";
  }
  print();
  if (!lit.polarity()) {
    out << ")";
  }
  return out;
}


bool TestUtils::isAC(Term* t) 
{
  auto f = t->functor();
  if (t->isLiteral()) {
    return theory->isInterpretedPredicate(f) && isAC(theory->interpretPredicate(f));
  } else {
    return theory->isInterpretedFunction(f) && isAC(theory->interpretFunction(f));
  }
}
bool TestUtils::isAC(Theory::Interpretation i) 
{
  switch (i) {
#define NUM_CASE(oper) \
    case Kernel::Theory::INT_  ## oper: \
    case Kernel::Theory::REAL_ ## oper: \
    case Kernel::Theory::RAT_  ## oper

    NUM_CASE(PLUS):
    NUM_CASE(MULTIPLY):
    case Kernel::Theory::EQUAL:
      return true;
    default: 
      return false;

#undef NUM_CASE
  }
}

bool TestUtils::eqModAC(const Kernel::Clause* lhs, const Kernel::Clause* rhs)
{ return permEq(*lhs, *rhs, [](Literal* l, Literal* r) -> bool { return TestUtils::eqModAC(l, r); }); }

bool TestUtils::eqModAC(Kernel::Literal* lhs, Kernel::Literal* rhs)
{ return TestUtils::eqModAC(TermList(lhs), TermList(rhs)); }

// bool TestUtils::eqModACVar(Kernel::Literal* lhs, Kernel::Literal* rhs, RectMap& map)
// { return TestUtils::eqModACVar(TermList(lhs), TermList(rhs), map); }

void __collect(unsigned functor, Term* t, Stack<TermList>& out) {
  ASS_EQ(t->functor(), functor);
  for (unsigned i = 0; i < t->arity(); i++) {
    auto trm = t->nthArgument(i);
    if (trm->isVar()) {
      out.push(*trm);
    } else {
      ASS(trm->isTerm());
      if (trm->term()->functor() == functor) {
        __collect(functor, trm->term(), out);
      } else {
        out.push(*trm);
      }
    }
  }
}

Stack<TermList> collect(unsigned functor, Term* t) {
  Stack<TermList> out;
  __collect(functor, t, out);
  return out;
}


template<class Comparisons>
bool TestUtils::eqModAC_(TermList lhs, TermList rhs, Comparisons comp)
{
  if (lhs.isVar() && rhs.isVar()) {
    return comp.var(lhs.var(), rhs.var());
  } else if (lhs.isTerm() && rhs.isTerm()) {
    auto& l = *lhs.term();
    auto& r = *rhs.term();
    if ( l.functor() != r.functor() ) return false;
    auto fun = l.functor();
    if (isAC(&l)) {
      Stack<TermList> lstack = collect(fun, &l);
      Stack<TermList> rstack = collect(fun, &r);
      return permEq(lstack, rstack, [&](TermList l, TermList r) -> bool {
            return comp.subterm(l, r);
      });
    } else {
      for (unsigned i = 0; i < l.arity(); i++) {
        if (!comp.subterm(*l.nthArgument(i), *r.nthArgument(i))) {
          return false;
        }
      }
      return true;
    }
  } else {
    return false;
  }
}

bool TestUtils::eqModAC(TermList lhs, TermList rhs) 
{
  struct Comparisons {
    bool var(unsigned lhs, unsigned rhs) const 
    { return lhs == rhs; }

    bool subterm(TermList lhs, TermList rhs) const 
    { return eqModAC(lhs,rhs); }
  };
  Comparisons c {};

  return eqModAC_(lhs, rhs, c);
}

} // namespace Test
