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
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "ArgCong.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ArgCong::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, Ordering* ord = nullptr)
      : /*_afterCheck(afterCheck), _ord(ord),*/ _cl(cl), _freshVar(cl->maxVar() + 1) {}

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
      alpha1 = *eqSort.term()->nthArgument(0);
      alpha2 = *eqSort.term()->nthArgument(1);
    }

    auto freshVar = TermList::var(_freshVar);
    auto lhs = lit->termArg(0);
    auto rhs = lit->termArg(1);
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

        if (sortIsVar /*&& _afterCheck && _cl->numSelected() > 1*/) {
          currAfter = SubstHelper::apply(curr, subst);
          /*

          if (i < _cl->numSelected() && _ord->compare(currAfter,newLit) == Ordering::GREATER) {
            env.statistics->inferencesBlockedDueToOrderingAftercheck++;
            return 0;
          }*/ //TODO reintroduce check
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
  // currently unused
  // bool _afterCheck;
  // Ordering* _ord;
  Clause* _cl;
  unsigned _freshVar;
};

ClauseIterator ArgCong::generateClauses(Clause* premise)
{
  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS_G(premise->numSelected(),0);

  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) { return l->isEquality() && l->isPositive(); })
    .map(ResultFn(premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      &_salg->getOrdering()))
    .filter(NonzeroFn()));
}

}
