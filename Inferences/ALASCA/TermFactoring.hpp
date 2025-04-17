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
 * @file TermFactoring.hpp
 * Defines class TermFactoring
 *
 */

#ifndef __TermFactoring__
#define __TermFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/ALASCA.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Shell/Options.hpp"
#include "Lib/Output.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TermFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(TermFactoring);

  TermFactoring(TermFactoring&&) = default;
  TermFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  struct Application : public SelectedAtomicTermItpAny {
    Application(SelectedAtomicTermItpAny self) : SelectedAtomicTermItpAny(std::move(self)) {}

    SelectionCriterion            literalMaximality() const { return SelectionCriterion::NOT_LESS; }
    SelectionCriterion    localAtomicTermMaximality() const { return SelectionCriterion::NOT_LESS; }
    SelectionCriterion   globalAtomicTermMaximality() const { return SelectionCriterion::NOT_LESS; }

    static auto iter(AlascaState& shared, __SelectedLiteral sel) {
      return SelectedAtomicTermItpAny::iter(shared.ordering, sel, SelectionCriterion::NOT_LESS)
              .filter([](auto& x) { return !x.selectedAtomicTerm().isVar(); })
              .map([&]  (auto selected) { return Application(std::move(selected)); });
    }

    // static auto iter(AlascaState& shared, SelectedAtom const& sel) {
    //   return iterTraits(sel.toSelectedAtomicTermItp()
    //           .map([&]  (auto selected) { return Application(std::move(selected)); })
    //           .intoIter());
    // }

    // TODO 2 depreacte
    static auto iter(AlascaState& shared, Clause* cl) 
    { return shared.selected(cl)
              .flatMap([&shared](auto selected) { return iter(shared, selected); }); }
    
    auto iterSecond(AlascaState& shared) {
      return coproductIter(this->applyCo([shared](auto self) {
        auto t1 = self.selectedSummand();
        auto termIdx = self.termIdx();
        return range(0, self.alascaLiteral().term().nSummands())
           .dropNth(termIdx)
           .filter([termIdx](auto i) { return i < termIdx;  }) // <- symmetry breaking
           .filterMap([shared,self,t1](auto i) {
             auto t2 = self.alascaLiteral().term().summandAt(i);
             return someIf(/* no unshielded vars */ !t2.atom().isVar(),
                 [&](){ return shared.unify(t1.atom(), t2.atom());
                 }).flatten()
                 .map([&](auto unif) { return std::make_tuple(i, std::move(unif)); });
           });
      }));
    }
  };

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  static Clause* applyRule(Application const& appl, unsigned i, AbstractingUnifier& unif) {
    return appl.apply([&](auto self) {
        auto n = self.numTraits();
        auto lit = self.alascaLiteral();

        auto s = self.selectedSummand().atom();
        auto j = self.selectedSummand().numeral();
        auto k = lit.term().summandAt(i).numeral();
    Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_TERM_FACTORING, self.clause()));
    return Clause::fromIterator(concatIters(

          iterItems(
            createLiteral<decltype(n)>(lit.symbol(), n.sum(
                concatIters(
                  iterItems(AlascaMonom<decltype(n)>(j + k , s)),
                  lit.term().iterSummands()
                    .dropNth(std::max(i, appl.termIdx()))
                    .dropNth(std::min(i, appl.termIdx()))
                  )
                  .map([&](auto ti) -> TermList { return AlascaMonom<decltype(n)>(ti.numeral(), unif.subs().apply(ti.atom(), 0)).toTerm(); })
            ))
          ),
          self.contextLiterals()
             .map([&](auto l) { return unif.subs().apply(l, /* bank */ 0); }),
          arrayIter(unif.computeConstraintLiterals())
          ),inf);
    });
  }

  ClauseIterator generateClauses(Clause* premise) final override {
    return pvi(Application::iter(*_shared, premise)
        .inspect([](auto& appl) { DEBUG(0, "appl: ", appl); })
        .flatMap([=](auto sel) { 
          return sel.iterSecond(*_shared)
                    .inspect([](auto& unif) { DEBUG(0, "  unif: ", unif); })
                    .filter([=](auto& unif) { 
                        // TODO 2 remove this call and replace by DSL call
                        return _shared->selector.postUnificationCheck(sel, /* varBank */ 0, std::get<1>(unif), _shared->ordering, [](auto&& msg) { DEBUG(0, "  no result: ", msg) }); })
                    .map([sel](auto i_unif) {
                        return applyRule(sel, std::get<0>(i_unif), std::get<1>(i_unif));
                    })
                    .inspect([&](auto& r) { DEBUG(0, "  result: ", *r) })
                    ;
        }));
  }

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override
  { return pvi(dropElementType(Application::iter(*_shared, selection)
        .flatMap([=](auto sel) { return sel.iterSecond(*_shared); }))); }
private:
  template<class NumTraits> Option<Clause*> applyRule(SelectedAtomicTermItp<NumTraits> const& l, SelectedAtomicTermItp<NumTraits>const& r);
  std::shared_ptr<AlascaState> _shared;
};

} // namespace ALASCA 
} // namespace Inferences 
#undef DEBUG

#endif /*__TermFactoring__*/
