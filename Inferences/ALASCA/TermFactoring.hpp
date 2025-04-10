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

    static SelectionCriterion literalMaximality() { return SelectionCriterion::NOT_LESS; }
    static SelectionCriterion    atomMaximality() { return SelectionCriterion::NOT_LESS; }

    static auto iter(AlascaState& shared, __SelectedLiteral sel) {
      return SelectedAtomicTermItpAny::iter(shared.ordering, sel, literalMaximality(), atomMaximality())
              .map([&]  (auto selected) { return Application(std::move(selected)); });
    }

    static auto iter(AlascaState& shared, SelectedAtom const& sel) {
      return iterTraits(sel.toSelectedAtomicTermItp()
              .map([&]  (auto selected) { return Application(std::move(selected)); })
              .intoIter());
    }

    static auto iter(AlascaState& shared, Clause* cl) 
    { 
      return shared.selected(cl, /* literal*/ SelectionCriterion::NOT_LESS,
                                 /* term */ SelectionCriterion::NOT_LESS,
                                 /* include number vars */ false)
              .flatMap([&shared](auto selected) { return iter(shared, selected); });
    }
    
    auto iterSecond(AlascaState& shared) {
      return coproductIter(this->applyCo([&shared](auto self) {
        auto t1 = self.selectedSummand();
        auto termIdx = self.termIdx();
        auto pos1 = t1.numeral() > 0;
        return range(0, self.alascaLiteral().term().nSummands())
           .dropNth(termIdx)
           .filter([termIdx](auto i) { return i < termIdx;  }) // <- symmetry breaking
           .map([self](auto i) { return self.alascaLiteral().term().summandAt(i); })
           .filter([pos1](auto& t2) { return pos1 || t2.numeral() > 0; })
           .filterMap([&shared,t1](auto t2) {
             return shared.unify(t1.atom(), t2.atom());
           });
      }));
    }
  };

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  ClauseIterator generateClauses(Clause* premise) final override {
    return pvi(Application::iter(*_shared, premise)
        .inspect([](auto& appl) { DEBUG(0, "appl: ", appl); })
        .flatMap([=](auto sel) { 
          return sel.iterSecond(*_shared)
                    .inspect([](auto& unif) { DEBUG(0, "  unif: ", unif); })
                    .filter([=](auto& unif) { 
                        return _shared->selector.postUnificationCheck(sel, /* varBank */ 0, unif, _shared->ordering, [](auto&& msg) { DEBUG(0, "  no result: ", msg) }); })
                    .map([sel](auto unif) {
                        Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_TERM_FACTORING, sel.clause()));
                        return Clause::fromIterator(concatIters(
                              sel.clause()->iterLits()
                                 .map([&](auto l) { return unif.subs().apply(l, /* bank */ 0); }),
                              arrayIter(unif.computeConstraintLiterals())
                              ),inf);
                    })
                    .inspect([&](auto& r) { DEBUG(0, "  result: ", *r) })
                    ;
        }));
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {  }
#endif

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
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
