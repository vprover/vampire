
/*
 * File TestUtils.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TestUtils.cpp
 * Implements class TestUtils.
 */

#include <cstdarg>


#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"

// #include "Shell/AIG.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"

#include "TestUtils.hpp"

namespace Test
{

using namespace Kernel;
using namespace Shell;

// Formula* TestUtils::getUniqueFormula(UnitList* units)
// {
//   CALL("TestUtils::getUniqueFormula(UnitList*)");
//
//   FormulaList* forms = 0;
//   UnitList::Iterator uit(units);
//   while(uit.hasNext()) {
//     Unit* u = uit.next();
//     Formula* form = u->getFormula();
//     FormulaList::push(form, forms);
//   }
//   Formula* conj;
//   if(forms==0) {
//     conj = new Formula(true);
//   }
//   else if(forms->tail()==0) {
//     conj = forms->head();
//   }
//   else {
//     conj = new JunctionFormula(AND, forms);
//   }
//
//   static AIGFormulaSharer sharer;
//   return sharer.apply(conj).first;
// }
//
// Formula* TestUtils::getUniqueFormula(Api::AnnotatedFormulaIterator afit)
// {
//   CALL("TestUtils::getUniqueFormula(Api::AnnotatedFormulaIterator)");
//
//   UnitList* units = 0;
//   while(afit.hasNext()) {
//     Api::AnnotatedFormula af = afit.next();
//     UnitList::push(static_cast<Unit*>(af), units);
//   }
//   Formula* res = getUniqueFormula(units);
//   units->destroy();
//   return res;
// }
//
// Formula* TestUtils::getUniqueFormula(Api::Problem prb)
// {
//   CALL("TestUtils::getUniqueFormula(Api::Problem)");
//
//   return TestUtils::getUniqueFormula(prb.formulas());
// }

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

template<class List, class Eq>
bool __permEq(const List& lhs, const List& rhs, Eq elemEq, DArray<unsigned>& perm, unsigned idx) {
  auto checkPerm = [&] (const List& lhs, const List& rhs, DArray<unsigned>& perm) {
    ASS_EQ(lhs.size(), perm.size());
    ASS_EQ(rhs.size(), perm.size());

    for (int i = 0; i < perm.size(); i++) {
      if (!elemEq(lhs[i], rhs[perm[i]])) return false;
    }
    return true;
  };
  if (checkPerm(lhs, rhs, perm)) {
    return true;
  }
  for (int i = idx; i < perm.size(); i++) {
    swap(perm[i], perm[idx]);


    if (__permEq(lhs,rhs, elemEq, perm, idx+1)) return true;

    swap(perm[i], perm[idx]);
  }

  return false;
}


template<class List, class Eq>
bool TestUtils::permEq(const List& lhs, const List& rhs, Eq elemEq) 
{
  ASS_EQ(lhs.size(), rhs.size());
  DArray<unsigned> perm(lhs.size());
  for (int i = 0; i < lhs.size(); i++) {
    perm[i] = i;
  }
  return __permEq(lhs, rhs, elemEq, perm, 0);
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
{
  return permEq(*lhs, *rhs, [](Literal* l, Literal* r) -> bool { return TestUtils::eqModAC(l, r); });
}

bool TestUtils::eqModAC(Kernel::Literal* lhs, Kernel::Literal* rhs)
{
  return TestUtils::eqModAC(TermList(lhs), TermList(rhs)); 
}

void __collect(unsigned functor, Term* t, Stack<TermList>& out) {
  ASS_EQ(t->functor(), functor);
  for (int i = 0; i < t->arity(); i++) {
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


bool TestUtils::eqModAC(TermList lhs, TermList rhs) 
{

  if (lhs.isVar() && rhs.isVar()) {
    return lhs.var() == rhs.var();
  } else if (lhs.isTerm() && rhs.isTerm()) {
    auto& l = *lhs.term();
    auto& r = *rhs.term();
    if ( l.functor() != r.functor() ) return false;
    auto fun = l.functor();
    if (theory->isInterpretedFunction(fun) && isAC(theory->interpretFunction(fun))) {
      Stack<TermList> lstack = collect(fun, &l);
      Stack<TermList> rstack = collect(fun, &r);
      return permEq(lstack, rstack, [](TermList l, TermList r) -> bool {
            return eqModAC(l, r);
      });
    } else {
      for (int i = 0; i < l.arity(); i++) {
        if (!eqModAC(*l.nthArgument(i), *r.nthArgument(i))) {
          return false;
        }
      }
      return true;
    }
  } else {
    return false;
  }
}

}
