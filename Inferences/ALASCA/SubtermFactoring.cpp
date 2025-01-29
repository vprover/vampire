/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "SubtermFactoring.hpp"
#include "Inferences/ALASCA/Superposition.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

struct Application 
{
  TermList _activePos;
  AnyPoly _sum;
  unsigned i;
  unsigned j;
  
  friend std::ostream& operator<<(std::ostream& out, Application const& self)
  { return out << self._activePos << " @ unify(" << self.term1() << ", " << self.term2()  << ")"; }

  TermList termAt(unsigned i) const { return _sum.apply([&](auto& s) { return s->summandAt(i).factors->denormalize(); }); }
  TermList term1() const { return termAt(i); }
  TermList term2() const { return termAt(j); }

  static auto iter(AlascaState& shared, Clause* cl)
  {
    return ALASCA::Superposition::Rhs::activePositions(shared, cl)
      .flatMap([&](auto sel_lit) {
          return coproductIter(sel_lit.map(
             [](SelectedSummand& x) { return iterItems(x.selectedAtom()); },
             [](SelectedUninterpretedEquality& x) {  return iterItems(x.biggerSide()); },
             [](SelectedUninterpretedPredicate& x) { return termArgIter(x.literal()); }
          ))
          .flatMap([&](auto activePos) {
            return shared.iterInterpretedSubterms(activePos)
               .flatMap([=](auto t_anyNum) {
                   return coproductIter(t_anyNum.applyCo([=](auto t) {
                       return range(0, t->nSummands() - 1)
                          .flatMap([=](auto i) {
                              return range(i + 1, t->nSummands())
                                .map([=](auto j) {
                                   return Application { ._activePos = activePos, ._sum = t_anyNum, .i = i, .j = j, };
                                })
                                .inspect([](auto& a) { DEBUG(a) })
                                .filter([](auto& appl) { return appl.term1().isTerm()
                                                              && appl.term2().isTerm()
                                                              && appl.term1().term()->functor() == appl.term2().term()->functor()
                                                              ;  })
                                ;
                          })
                          ;
                   })); 
               });
              }) ;
      })
    ;
  }
};

ClauseIterator SubtermFactoring::generateClauses(Clause* premise)
{
  return pvi(Application::iter(*_shared, premise)
    .filterMap([=](auto appl) {
        return _shared->unify(appl.term1(), appl.term2())
          .map([&](auto unif) {
              return Clause::fromIterator(
                  concatIters(
                    premise->iterLits()
                      .map([&](auto l) { return unif.subs().apply(l, 0); }),
                    arrayIter(unif.computeConstraintLiterals())
                    ),
                  Inference(GeneratingInference1(Kernel::InferenceRule::ALASCA_TERM_FACTORING, premise))
                  );
          });
    }));
}

} // namespace ALASCA
} // namespace Inferences
