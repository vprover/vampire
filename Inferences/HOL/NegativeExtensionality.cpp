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

#include "Debug/TimeProfiling.hpp"

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Lib/DHMap.hpp"
#include "Shell/InferenceRecorder.hpp"
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

void getVarSorts(TypedTermList t, DHMap<unsigned,TermList, FnvHash, IdentityHash>& varSorts)
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
    ASS(lit->isNegative());

    auto eqSort = lit->eqArgSort();
    if (eqSort.isVar() || !eqSort.isArrowSort()) { return nullptr; }
    auto [lhs, rhs] = lit->eqArgs();
    TermList alpha1 = eqSort.domain();
    TermList alpha2 = eqSort.result();
    static DHMap<unsigned,TermList, FnvHash, IdentityHash> varSorts;
    varSorts.reset();

    getVarSorts(TypedTermList(lhs, eqSort), varSorts);
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

    TermList resultSort = alpha1;
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    SortHelper::normaliseSort(typeVars, resultSort);

    auto skSymSort = AtomicSort::arrowSort(termVarSorts, resultSort);
    unsigned fun;
    TermList recordedWitness;
    if (env.reconstruction) {
      recordedWitness = Shell::InferenceRecorder::instance()->replayWitness(lit,
          Shell::InferenceRecorder::InferenceInformation::WitnessKind::EXTENSIONALITY);
      if (recordedWitness.isEmpty()) { return nullptr; }
      auto [head, args] = HOL::getHeadAndArgs(recordedWitness);
      fun = head.term()->functor();
      auto type = env.signature->getFunction(fun)->type();
      if (type->arity() != typeVars.size() || type->result() != skSymSort) { return nullptr; }
    } else {
      fun = Skolem::addSkolemFunction(typeVars.size(), TermStack(), skSymSort)->number();
    }
    auto head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
    auto skolemTerm = HOL::create::app(head, termVars);
    // Replay uses the same dependency calculation as search. Reusing a
    // symbol must not make a different dependency list an accepted candidate.
    if (env.reconstruction && skolemTerm != recordedWitness) { return nullptr; }

    auto newLit = Literal::createEquality(false,
      HOL::create::app(alpha1, alpha2, lhs, skolemTerm),
      HOL::create::app(alpha1, alpha2, rhs, skolemTerm),
    alpha2);

    RStack<Literal*> resLits;

    for (const auto& curr : *_cl) {
      resLits->push(curr == lit ? newLit : curr);
    }

    auto result = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::NEGATIVE_EXTENSIONALITY, _cl));
    if (env.reconstruction) {
      Shell::InferenceRecorder::instance()->witness(
          Shell::InferenceRecorder::InferenceInformation::WitnessKind::EXTENSIONALITY,
          result, _cl, lit, skolemTerm);
    }
    return result;
  }
private:
  Clause* _cl;
};

ClauseIterator NegativeExtensionality::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) { return l->isEquality() && l->isNegative(); })
    .map(NegExtResultFn(premise))
    .filter(NonzeroFn())
    .timeTraced("negative extensionality"));
}

}
