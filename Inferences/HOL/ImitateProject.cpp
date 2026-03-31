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
 * @file ImitateProject.cpp
 * Implements class ImitateProject.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/HOL/HOL.hpp"

#include "ImitateProject.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ImitateProjectFn
{
  ImitateProjectFn(Clause* cl) : _cl(cl), _maxVar(cl->maxVar()) {}

  ClauseIterator operator() (Literal* lit)
  {
    static ClauseStack results;
    results.reset();

    auto [lhs, rhs] = lit->eqArgs();

    auto flexTerm = lhs.head().isVar() ? lhs : rhs;
    auto rigidTerm = lhs.head().isVar() ? rhs : lhs;

    TermList headFlex = flexTerm.head();
    auto pushResult = [this,headFlex](TermList binding, InferenceRule rule)
    {
      static Substitution subst;
      subst.reset();
      subst.bind(headFlex.var(), binding);
      results.push(Clause::fromIterator(
        _cl->iterLits().map([](Literal* lit) { return SubstHelper::apply(lit, subst); }),
        GeneratingInference1(rule, _cl)));
    };

    for (const auto& [binding, inf] : HOL::getProjAndImitBindings(flexTerm, rigidTerm, _maxVar)) {
      pushResult(binding, inf == HOL::UnificationInference::IMITATION ? InferenceRule::IMITATION : InferenceRule::PROJECTION);
    }

    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));;
  }
private:
  Clause* _cl;
  unsigned _maxVar;
};

ClauseIterator ImitateProject::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) {
      ASS(l->isEquality());
      return l->isFlexRigid() && !l->polarity();
      // TODO decide whether to keep check below (see NegExt)
      /*&& !SortHelper::getEqualityArgumentSort(l).isArrowSort()*/;
    })
    .flatMap(ImitateProjectFn(premise)));
}

}
