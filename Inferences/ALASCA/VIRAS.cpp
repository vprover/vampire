/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "VIRAS.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/NumTraits.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Option.hpp"
#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

using namespace Kernel;
using namespace Inferences;
using namespace ALASCA;
using namespace Lib;

#include "VirasInterfacing.hpp"

/* turns a viras::iter iterator into a Lib/Metaiterators.hpp iterator */
template<class VirasIter>
class IntoVampireIter {
  VirasIter _iter;
  Option<std::optional<viras::iter::value_type<VirasIter>>> _next;
public:
  IntoVampireIter(VirasIter iter) : _iter(std::move(iter)), _next() {}

  DECL_ELEMENT_TYPE(viras::iter::value_type<VirasIter>);
  void loadNext() {
    if (_next.isNone()) {
      _next = some(_iter.next());
    }
  }

  bool hasNext() {
    loadNext();
    return bool(*_next);
  }

  viras::iter::value_type<VirasIter> next() {
    loadNext();
    return std::move(*_next.take().unwrap());
  }
};

template<class VirasIter>
auto intoVampireIter(VirasIter i)
{ return iterTraits(IntoVampireIter<VirasIter>(std::move(i))); }

struct Void {};

template<class NumTraits, class F>
void traverseLiraVars(TermList self, F f) {
  VampireVirasConfig<NumTraits>{}.
    matchTerm(self,
      /* var v */ [&](auto y) { f(y); return Void {}; },
      /* numeral 1 */ [&]() { return Void {}; },
      /* k * t */ [&](auto k, auto t)  { traverseLiraVars<NumTraits>(t, f); return Void {}; },
      /* l + r */ [&](auto l, auto r)  {
        traverseLiraVars<NumTraits>(l, f);
        traverseLiraVars<NumTraits>(r, f);
        return Void {};
      },
      /* floor */ [&](auto t) { traverseLiraVars<NumTraits>(t, f); return Void {}; }
      );
}


template<class NumTraits>
Option<SimplifyingGeneratingInference::ClauseGenerationResult> VirasQuantifierElimination::generateSimplify(NumTraits n, Clause* premise) {
  DEBUG(0, *premise)
  auto viras = viras::viras(VampireVirasConfig<NumTraits>{});
  Recycled<DHSet<unsigned>> shieldedVars;
  Recycled<DHSet<unsigned>> candidateVars;
  Recycled<Stack<Literal*>> toElim;
  Recycled<Stack<Literal*>> otherLits;
  auto noteShielded = [&](Term* t) {
    VariableIterator vars(t);
    while (vars.hasNext()) {
      auto v = vars.next();
      shieldedVars->insert(v.var());
    }
  };

  Recycled<DHSet<unsigned>> topLevelVars;
  for (auto l : premise->iterLits()) {
    Option<AlascaLiteral<NumTraits>> norm = _shared->norm().tryNormalizeInterpreted(l)
      .flatMap([](auto l) { return l.template as<AlascaLiteral<NumTraits>>().toOwned(); })
      .filter([](auto l) { switch(l.symbol()) {
          case AlascaPredicate::EQ:
          case AlascaPredicate::NEQ:
          case AlascaPredicate::GREATER:
          case AlascaPredicate::GREATER_EQ: return true;
          }
          ASSERTION_VIOLATION
          });

    if (norm.isNone()) {
      otherLits->push(l);
      noteShielded(l);
    } else {
      toElim->push(l);
      traverseLiraVars<NumTraits>(norm->term().denormalize(),
          [&](TermList t) {
            if (t.isVar()) {
              candidateVars->insert(t.var());
            } else {
              noteShielded(t.term());
            }
          });
    }
  }

  auto unshielded = iterTraits(candidateVars->iterator())
    .filter([&](auto x) { return !shieldedVars->contains(x); })
    .tryNext();

  if (unshielded.isNone()) {
    return {};
  } else {
    auto var = typename VampireVirasConfig<NumTraits>::VarWrapper(TermList::var(*unshielded));
    return some(ClauseGenerationResult {
      .clauses = pvi(
          intoVampireIter(viras.quantifier_elimination(var, &*toElim))
            .map([premise, otherLits = std::move(otherLits)](auto litIter) {
              return Clause::fromIterator(
                  concatIters(
                    intoVampireIter(litIter),
                    otherLits->iter()
                    ),
                  Inference(SimplifyingInference1(InferenceRule::ALASCA_VIRAS_QE, premise)));
            })
          )
        ,
      .premiseRedundant = true,
    });
  }
}

Option<SimplifyingGeneratingInference::ClauseGenerationResult> VirasQuantifierElimination::generateSimplify(IntTraits n, Clause* premise) {
  // TODO viras for integers ? (=  cooper)
  return {};
}

SimplifyingGeneratingInference::ClauseGenerationResult VirasQuantifierElimination::generateSimplify(Clause* premise) {
  return 
    forAnyNumTraits([&](auto n) { return generateSimplify(n, premise); })
    .unwrapOrElse([]() {
      return ClauseGenerationResult {
        .clauses = VirtualIterator<Clause*>::getEmpty(),
        .premiseRedundant = false,
      };
    });
}

