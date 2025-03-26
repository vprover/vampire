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
 * @file VariableElimination.hpp
 * Defines class VariableElimination
 *
 */

#ifndef __Inferences_ALASCA_ABSTRACTION__
#define __Inferences_ALASCA_ABSTRACTION__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/EqHelper.hpp"
#include <type_traits>


namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Abstraction
: public ImmediateSimplificationEngine
{

public:

  template<class N, class F1, class F2>
  std::invoke_result_t<F1, TermList> iterUninterpretedOrVarSummands(
      AlascaTermItp<N> term, 
      F1 var,
      F2 nonVar
      ) 
  {
    for (AlascaMonom<N> s : term.iterSummands()) {
      std::invoke_result_t<F1, TermList> result;
      if (s.atom().isVar()) {
        result = var(s.atom());
      } else if (N::isFloor(s.atom().term()->functor())) {
        auto normArg = AnyAlascaTerm::normalize(TypedTermList(s.atom().term()->termArg(0), N::sort()))
            .template asSum<N>().unwrap();
        result = iterUninterpretedOrVarSummands(normArg, var, nonVar);
      } else {
        result = nonVar(s.atom().term());
      }
      if (result) {
        return result;
      }
    }
    return {};
  }

  Clause* applyAbstraction(Clause* clause, TypedTermList toAbstract) {

    auto maxVar = clause->iterLits()
          .flatMap([&](auto x) { return VariableIterator(x); })
          .map([&](auto t) { return t.var(); })
          .max()
          .unwrap();
    auto newVar = TermList::var(1 + maxVar);

    return Clause::fromIterator(
      concatIters(
        iterItems(Literal::createEquality(false, newVar, toAbstract, toAbstract.sort())),
        clause->iterLits()
         .map([&](auto l) -> Literal* {
           return EqHelper::replace(l, toAbstract, newVar);
         })
       ),
       Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_ABSTRACTION, clause)));
  }

  Option<Clause*> trySimplifiy(Clause* premise, Term* termOrLit)  {
    for (auto a : termArgIterTyped(termOrLit)) {
      auto normA = AnyAlascaTerm::normalize(a);
      for (auto subterm : normA.topDownIter()) {
        if (auto itp = subterm.asSum()) {
          auto result = itp->apply([&](auto itp) -> Option<Clause*> {

              // if (itp.nSummands() == 1 && itp[0].atom().isVar()) {
              //   return {};
              // }

              if (itp.asVar().isSome()) {
                return {};
              }

              auto unshieldedVar = iterUninterpretedOrVarSummands(itp, 
                  [&](TermList var) { return true; }, 
                  [&](Term*       ) { return false; });

              if (unshieldedVar) {
                return some(applyAbstraction(premise, subterm.toTerm()));
              } else {
                return {};
              }
          });
          if (result) {
            return result;
          }
        }
      }
    }
    return {};
  }

  virtual Clause* simplify(Clause* premise) final override {
    if (premise->size() == 0) {
      // TODO why do we ever get the empty clause here?
      return premise;
    }
    // TODO get rid of this set
    Recycled<Set<TermList>> topLevelVars;
    auto todo = RStack<Term*>();
    for (auto lit : premise->iterLits()) {
      auto norm = InequalityNormalizer::normalize(lit);
      Option<Clause*> result;
      if (auto itp = norm.asItp()) {
        result = itp->apply([&](auto itp) {
            return iterUninterpretedOrVarSummands(itp.term(), 
                [&](TermList v) { return Option<Clause*>{}; },
                [&](Term*    t) { return trySimplifiy(premise, t); });
        });
      } else {
        result = trySimplifiy(premise, lit);
      }
      if (result) {
        return *result;
      }
    }
    return premise;
  }

};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_ABSTRACTION__*/
