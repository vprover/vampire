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
 * @file NegativeExtensionality.cpp
 * Implements class NegativeExtensionality.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Lib/DHMap.hpp"
#include "Shell/Skolem.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NegativeExtensionality.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void getVarSorts(TypedTermList t, DHMap<unsigned,TermList>& varSorts)
{
  if (t.isVar()) {
    varSorts.insert(t.var(), t.sort());
    return;
  }
  for (const auto& [v, s] : iterTraits(VariableWithSortIterator(t.term()))) {
    varSorts.insert(v.var(),s);
  }
}

struct NegExtResultFn
{
  NegExtResultFn(Clause* cl) : _cl(cl) {}

  Clause* operator() (Literal* lit)
  {
    ASS(lit->isEquality());
    ASS(!lit->isPositive());

    static DHMap<unsigned,TermList> varSorts;
    varSorts.reset();

    auto eqSort = SortHelper::getEqualityArgumentSort(lit);
    if (eqSort.isVar() || !eqSort.isArrowSort()) {
      return nullptr;
    }

    auto lhs = lit->termArg(0);
    getVarSorts(TypedTermList(lhs, eqSort), varSorts);

    auto rhs = lit->termArg(1);
    getVarSorts(TypedTermList(rhs, eqSort), varSorts);

    if (lit->isTwoVarEquality()) {
      getVarSorts(TypedTermList(eqSort, AtomicSort::superSort()), varSorts);
    }

    TermStack termVarSorts;
    TermStack termVars;
    TermStack typeVars;

    for (const auto& [var, sort] : iterTraits(varSorts.items())) {
      if (sort == AtomicSort::superSort()){
        typeVars.push(TermList::var(var));
      } else {
        termVarSorts.push(sort);
        termVars.push(TermList::var(var));
      }
    }

    TermList alpha1 = *eqSort.term()->nthArgument(0);
    TermList alpha2 = *eqSort.term()->nthArgument(1);

    TermList resultSort = alpha1;
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    SortHelper::normaliseSort(typeVars, resultSort);

    auto skSymSort = AtomicSort::arrowSort(termVarSorts, resultSort);
    auto fun = Skolem::addSkolemFunction(typeVars.size(), typeVars.size(), 0, skSymSort);
    auto head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
    auto skolemTerm = HOL::create::app(head, termVars);

    auto newLit = Literal::createEquality(false,
      HOL::create::app(alpha1, alpha2, lhs, skolemTerm),
      HOL::create::app(alpha1, alpha2, rhs, skolemTerm),
    alpha2);

    RStack<Literal*> resLits;

    for (const auto& curr : *_cl) {
      resLits->push(curr == lit ? newLit : curr);
    }

    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::NEGATIVE_EXTENSIONALITY, _cl));
  }
private:
  Clause* _cl;
};

ClauseIterator NegativeExtensionality::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) { return l->isEquality() && !l->isPositive(); })
    .map(NegExtResultFn(premise))
    .filter(NonzeroFn()));
}

}
