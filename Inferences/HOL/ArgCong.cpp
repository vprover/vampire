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
 * @file ArgCong.cpp
 * Implements class ArgCong.
 */

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SortHelper.hpp"

#include "ArgCong.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ArgCongResultFn
{
  ArgCongResultFn(Clause* cl) : _cl(cl), _freshVar(cl->maxVar() + 1) {}

  Clause* operator() (Literal* lit)
  {
    ASS(lit->isEquality());
    ASS(lit->isPositive());

    static Substitution subst;

    auto eqSort = SortHelper::getEqualityArgumentSort(lit);
    bool sortIsVar = eqSort.isVar();
    if(!sortIsVar && !eqSort.isArrowSort()){
      return 0;
    }

    TermList alpha1, alpha2;
    if(eqSort.isVar()){
      subst.reset();
      alpha1 = TermList::var(_freshVar+1);
      alpha2 = TermList::var(_freshVar+2);
      subst.bindUnbound(eqSort.var(), AtomicSort::arrowSort(alpha1, alpha2));
    } else {
      alpha1 = eqSort.domain();
      alpha2 = eqSort.result();
    }

    auto freshVar = TermList::var(_freshVar);
    auto [lhs, rhs] = lit->eqArgs();
    if(sortIsVar){
      lhs = SubstHelper::apply(lhs, subst);
      rhs = SubstHelper::apply(rhs, subst);
    }

    auto newLit = Literal::createEquality(true,
      HOL::create::app(alpha1, alpha2, lhs, freshVar),
      HOL::create::app(alpha1, alpha2, rhs, freshVar),
      alpha2
    );

    RStack<Literal*> resLits;

    for (auto curr : iterTraits(_cl->iterLits())) {
      if(curr!=lit) {
        Literal* currAfter;

        if (sortIsVar) {
          currAfter = SubstHelper::apply(curr, subst);
        } else {
          currAfter = curr;
        }

        resLits->push(currAfter);
      } else {
        resLits->push(newLit);
      }
    }

    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::ARG_CONG, _cl));
  }
private:
  Clause* _cl;
  unsigned _freshVar;
};

ClauseIterator ArgCong::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) { return l->isEquality() && l->isPositive(); })
    .map(ArgCongResultFn(premise))
    .filter(NonzeroFn()));
}

}
