/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "SubtermFactoring.hpp"
#include "Inferences/ALASCA/Superposition.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Inferences {
namespace ALASCA {

struct Application 
{
  // TODO is this _atom needed?
  SelectedAtom _atom;
  AlascaTermItpAny _sum;
  unsigned i;
  unsigned j;

  AlascaTermItpAny sum() const { return _sum; }
  
  friend std::ostream& operator<<(std::ostream& out, Application const& self)
  { return out << self._atom << " @ unify(" << self.term1() << ", " << self.term2()  << ")"; }

  TermList atomAt(unsigned i) const { return _sum.apply([&](auto& s) { return s.summandAt(i).atom(); }); }
  TermList term1() const { return atomAt(i); }
  TermList term2() const { return atomAt(j); }

  SelectionCriterion literalMaximality         () const { return Superposition::Rhs::literalMaximality(_atom); }
  SelectionCriterion localAtomicTermMaximality () const { return Superposition::Rhs::localAtomicTermMaximality(_atom); }
  SelectionCriterion globalAtomicTermMaximality() const { return Superposition::Rhs::globalAtomicTermMaximality(_atom); }

  static auto iter(AlascaState& shared_, __SelectedLiteral sel)
  {
    auto* shared = &shared_;
    return SelectedAtom::iter(shared->ordering, sel, SelectionCriterion::NOT_LESS)
      .flatMap([shared](auto atom) { 
          return atom.iterSelectedSubterms()
             .filterMap([](auto t) { return t.asSum(); })
             .filter([](auto& s) { return s.apply([](auto& s) { return s.nSummands() >= 2; }); })
             .flatMap([=](auto t_anyNum) {
                 return coproductIter(t_anyNum.applyCo([=](auto t) {
                     return range(0, t.nSummands() - 1)
                        .filter([=](auto i) { return !t.summandAt(i).isNumeral() && !t.summandAt(i).atom().isVar(); })
                        .flatMap([=](auto i) {
                            return range(i + 1, t.nSummands())
                              .filter([=](auto j) { return !t.summandAt(j).isNumeral() && !t.summandAt(j).atom().isVar(); })
                              .map([=](auto j) {
                                 return Application { ._atom = atom, ._sum = t_anyNum, .i = i, .j = j, };
                              })
                              .filter([](auto& appl) { return appl.term1().isTerm()
                                                            && appl.term2().isTerm()
                                                            && appl.term1().term()->functor() == appl.term2().term()->functor()
                                                            ;  })
                              .filterMap([=](auto appl) {
                                return shared->unify(appl.term1(), appl.term2())
                                  .map([&](auto unif) {
                                      return std::make_pair(std::move(appl), std::move(unif));
                                  });
                              });
                        });
                 })); 
             });
      });
   }


  // TODO 2 deprecate
  static auto iter(AlascaState& shared, Clause* cl)
  {
    return ALASCA::Superposition::Rhs::activePositions(shared, cl)
      .flatMap([&](auto atom) { return iter(shared, std::move(atom)); });
   }
};


VirtualIterator<std::tuple<>> SubtermFactoring::lookaheadResultEstimation(__SelectedLiteral const& selection) {
  return pvi(dropElementType(Application::iter(*_shared, selection)));
}

ClauseIterator SubtermFactoring::generateClauses(Clause* premise)
{
  return pvi(Application::iter(*_shared, premise)
    .inspect([](auto& rhs) { DEBUG(1, rhs) })
    // TODO 2 post unification checks
    .map([=](auto appl_unif) {
      auto appl = appl_unif.first;
      auto& unif = appl_unif.second;
      return appl.sum().apply([&](auto sum) {
        auto n = sum.numTraits();
        auto oldSum = sum.toTerm();

        auto s = sum.summandAt(appl.i).atom();
        auto j = sum.summandAt(appl.i).numeral();
        auto k = sum.summandAt(appl.j).numeral();
        auto newSum = n.sum(
                concatIters(
                  iterItems(AlascaMonom<decltype(n)>(j + k , s)),
                  sum.iterSummands()
                    .dropNth(std::max(appl.i, appl.j))
                    .dropNth(std::min(appl.i, appl.j)))
                  .map([&](auto ti) -> TermList { return ti.toTerm(); })
            );
          // TODO make its own InferenceRule (?)
        auto constr = unif.computeConstraintLiterals();
          return Clause::fromIterator(
              concatIters(
                premise->iterLits()
                  .map([&](auto l) { return unif.subs().apply(EqHelper::replace(l, oldSum, newSum), 0); }),
                arrayIter(*constr).cloned()
                ),
              Inference(GeneratingInference1(Kernel::InferenceRule::ALASCA_TERM_FACTORING, premise)));
      });
    }));
}

} // namespace ALASCA
} // namespace Inferences
