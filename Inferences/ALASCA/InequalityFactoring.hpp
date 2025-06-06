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
 * @file InequalityFactoring.hpp
 * Defines class InequalityFactoring
 *
 */

#ifndef __InequalityFactoring__
#define __InequalityFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Shell/Options.hpp"
#include "Lib/Metaiterators.hpp"
#include <utility>
#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityFactoring
: public GeneratingInferenceEngine
{
  using SArray = SmallArray<Clause*, 2>;
  using Iter = decltype(arrayIter(std::declval<SArray>()));
public:
  USE_ALLOCATOR(InequalityFactoring);

  InequalityFactoring(InequalityFactoring&&) = default;
  InequalityFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override;

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  template<class NumTraits>
  Iter generateClauses(Clause* premise, 
    Literal* lit1, AlascaLiteralItp<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, AlascaLiteralItp<NumTraits> l2, Monom<NumTraits> k_s2);

  template<class NumTraits>
  Iter applyRule(SelectedAtomicTermItp<NumTraits> const& l1, SelectedAtomicTermItp<NumTraits> const& l2, AbstractingUnifier& uwa);
  Iter applyRule(SelectedAtomicTermItpAny const& l1, SelectedAtomicTermItpAny const& l2, AbstractingUnifier& uwa);

  template<class NumTraits>
  Iter generateClauses(
      Clause* premise,
      Literal* lit1, AlascaLiteralItp<NumTraits> L1,
      Literal* lit2, AlascaLiteralItp<NumTraits> L2
    );

  ClauseIterator generateClauses(Clause* premise) final override;
  
private:
  std::shared_ptr<AlascaState> _shared;
};
#define _alascaFactoring true

struct InequalityFactoringDemod : ImmediateSimplificationEngine
{
  std::shared_ptr<AlascaState> _shared;
  InequalityFactoringDemod(std::shared_ptr<AlascaState> shared) : _shared(shared) {  }

  static const char* name() { return "alasca inequality factoring demodulation"; }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  Clause* simplify(Clause* premise) final override { ASSERTION_VIOLATION_REP("should only be used with simplifyMany")  }

  ClauseIterator simplifyMany(Clause* premise) final override 
  {
    if (auto result = apply(premise)) {
      DEBUG(0, premise->toString())
      DEBUG(0, "===============================")
      DEBUG(0, (*result)[0]->toString())
      DEBUG(0, (*result)[1]->toString())
      return pvi(arrayIter(std::move(*result)));
    } else {
      return VirtualIterator<Clause*>::getEmpty();
    }
  }


  // Variant 2
  //
  // C \/ s + t1 + t2 > 0 \/ s + t1 > 0
  // ===================
  // -t2 <  0 -> s + t1 + t2 > 0
  // -t2 == 0 -> s + t1 + t2 > 0
  // -t2 == 0 -> s + t1 > 0
  // -t2 >  0 -> s + t1 > 0
  // =======================
  // C \/ -t2 > 0 \/ s + t1 + t2 > 0
  // C \/  t2 > 0 \/ s + t1 > 0
  //
  //
  // ..............................
  //
  //
  // C \/ s + t1 + t2 >= 0 \/ s + t1 > 0
  // ===================
  // -t2 <  0 -> s + t1 + t2 >= 0
  // -t2 == 0 -> s + t1 + t2 >= 0
  // -t2 >  0 -> s + t1 > 0
  // =======================
  //  -t2 >  0 \/ s + t1 + t2 >= 0
  //   t2 >= 0 \/ s + t1 > 0
  //
  //
  // ..............................
  //
  //
  // C \/ s + t1 + t2 >= 0 \/ s + t1 >= 0
  // ===================
  // -t2 <  0 -> s + t1 + t2 >= 0
  // -t2 == 0 -> s + t1 + t2 >= 0
  // -t2 == 0 -> s + t1 >= 0
  // -t2 >  0 -> s + t1 >= 0
  // =======================
  //  -t2 >  0 \/ s + t1 + t2 >= 0
  //   t2 >  0 \/ s + t1 >= 0
  //  
  //
  // ..............................
  //
  //  
  // C \/ s + t1 + t2 > 0 \/ s + t1 >= 0
  // ===================
  // -t2 <  0 -> s + t1 + t2 > 0
  // -t2 == 0 -> s + t1 >= 0
  // -t2 >  0 -> s + t1 >= 0
  // =======================
  //  -t2 >= 0 \/ s + t1 + t2 > 0
  //   t2 >  0 \/ s + t1 >= 0
  //
  //
  // Variant 2
  // simplified
  //
  // C \/ s + t1 + t2 >~ 0 \/ s + t1 >~ 0
  // =======================
  // C \/ -t2 > 0 \/ s + t1 + t2 >~ 0
  // C \/  t2 > 0 \/ s + t1 >~ 0
  //
  //
  // ..............................
  //
  //
  // C \/ s + t1 + t2 >1 0 \/ s + t1 >2 0
  // ===================
  // -t2 <  0 -> s + t1 + t2 > 0
  // -t2 == 0 -> s + t1 >= 0
  // -t2 >  0 -> s + t1 >= 0
  // =======================
  //  -t2 ~>1 0 \/ s + t1 + t2 >1 0
  //   t2 ~>2  0 \/ s + t1 >2 0

  // Variant 1
  //
  // C \/ s > t1 \/ s > t2
  // ====================
  //        t2 <  t1 ==> s >  t2
  //        t2 == t1 ==> s >  t2
  //        t2 == t1 ==> s >  t1
  //        t2 >  t1 ==> s >  t1
  // ========================
  // C \/ t2 - t1 > 0 \/ s > t2
  // C \/ t1 - t2 > 0 \/ s > t1
  //
  // where
  // - s ≻ t2
  // - s ≻ t1
  //
  // ..............................
  //
  // C \/ s >= t1 \/ s > t2
  // ====================
  //        t2 <  t1 ==> s >  t2
  //        t2 == t1 ==> s >= t1
  //        t2 >  t1 ==> s >= t1
  // =========================
  // C \/ t2 - t1 >= 0 \/ s >  t2
  // C \/ t1 - t2 >  0 \/ s >= t1
  //
  // where
  // - s ≻ t2
  // - s ≻ t1
  //
  // ..............................
  //
  // C \/ s >= t1 \/ s >= t2
  // =====================
  //        t2 <  t1 ==> s >= t2
  //        t2 == t1 ==> s >= t2
  //        t2 == t1 ==> s >= t1
  //        t2 >  t1 ==> s >= t1
  // =========================
  // C \/ t2 - t1 >  0 \/ s >= t2
  // C \/ t1 - t2 >  0 \/ s >= t1
  //
  // where
  // - s ≻ t2
  // - s ≻ t1
  //
  // ..............................
  //
  // C \/ s >  t1 \/ s >= t2
  // =====================
  //        t2 <  t1 ==> s >= t2
  //        t2 == t1 ==> s >= t2
  //        t2 >  t1 ==> s >  t1
  // ========================
  // C \/ t2 - t1 >  0 \/ s >= t2
  // C \/ t1 - t2 >= 0 \/ s >  t1
  //
  // where
  // - s ≻ t2
  // - s ≻ t1
  //
  //
  ///////////////////////////////////////
  //  simplified:
  //
  // C \/ s >1 t1 \/ s >2 t2
  // ========================
  // C \/ t1 - t2 > 0 \/ s >1 t1
  // C \/ t2 - t1 > 0 \/ s >2 t2
  //
  // where
  // - >1 == >2
  // - s ≻ t2
  // - s ≻ t1
  //
  // ..............................
  //
  // C \/ s >= t1 \/ s > t2
  // =========================
  // C \/ t1 - t2 >  0 \/ s >= t1
  // C \/ t2 - t1 >= 0 \/ s >  t2
  //
  // where
  // - s ≻ t2
  // - s ≻ t1



  // tests
  //
  // think of numerals
  // think of negatives


  using SArray = SmallArray<Clause*, 2>;

  template<class NumTraits>
  Option<SArray> applyVariant2(Clause* cl,
      unsigned l1, AlascaLiteralItp<NumTraits> const& itp1,
      unsigned l2, AlascaLiteralItp<NumTraits> const& itp2) const 
  {
    if (!itp2.isInequality()) return {};


    RStack<AlascaMonom<NumTraits>> t1s;
    RStack<AlascaMonom<NumTraits>> t2s;

    auto iter1 = itp1.term().iterSummands();
    auto iter2 = itp2.term().iterSummands();
    Option<bool> itp1_is_superset;

    DEBUG_CODE(
        for (auto i : range(0, int(itp1.term().nSummands() - 1))) {
          ASS(itp1.term().summandAt(i).atom() <= itp1.term().summandAt(i + 1).atom());
        }
        for (auto i : range(0, int(itp2.term().nSummands() - 1))) {
          ASS(itp2.term().summandAt(i).atom() <= itp2.term().summandAt(i + 1).atom());
        }
    )
    Option<AlascaMonom<NumTraits>> tt1 = iter1.tryNext();
    Option<AlascaMonom<NumTraits>> tt2 = iter2.tryNext();
    while (tt1.isSome() && tt2.isSome()) {
      if (*tt1 == *tt2) {
        t1s->push(*tt1);
        tt1 = iter1.tryNext();
        tt2 = iter2.tryNext();
        continue;
      } 
      if (tt1->atom() == tt2->atom()) {
        /* not subsets */
        return {};
      }
      if (itp1_is_superset.isNone()) {
        itp1_is_superset = some(tt1->atom() < tt2->atom());
      }
      if (*itp1_is_superset) {
        if (tt1->atom() < tt2->atom()) {
          t2s->push(*tt1);
          tt1 = iter1.tryNext();
        } else {
          /* not subsets */
          return {};
        }
      } else {
        if (tt2->atom() < tt1->atom()) {
          t2s->push(*tt2);
          tt2 = iter2.tryNext();
        } else {
          /* not subsets */
          return {};
        }
      }
    }
    if (itp1_is_superset.isNone()) {
      itp1_is_superset = some(tt1.isSome());
    }
    if (*itp1_is_superset) {
      while (tt1.isSome()) {
        t2s->push(*tt1);
        tt1 = iter1.tryNext();
      }
      if (tt2.isSome()) {
        /* not subsets */
        return {};
      }
    } else {
      while (tt2.isSome()) {
        t2s->push(*tt2);
        tt2 = iter2.tryNext();
      }
      if (tt1.isSome()) {
        /* not subsets */
        return {};
      }
    }

#define CHECK_SETS(superset, subset)  \
    auto msg = Output::cat( \
            "t1: ", t1s, "\n", \
            "t2: ", t2s, "\n", \
            "superset: ", superset, "\n", \
            "subset: ", subset \
            ); \
      ASS_REP(t1s.size() + t2s.size() == superset.term().nSummands(), msg) \
      ASS_REP(t1s.size()             == subset.term().nSummands(), msg)\
      for (auto t : superset.term().iterSummands()) {\
        ASS_REP(t1s->find(t) || t2s->find(t), msg)\
      }\
      for (auto t : subset.term().iterSummands()) {\
        ASS_REP(t1s->find(t), msg)\
      }\


    DEBUG_CODE(
      if (*itp1_is_superset) {
        CHECK_SETS(itp1, itp2)
      } else {
        CHECK_SETS(itp2, itp1)
      }
    )
#undef CHECK_SETS

    
    auto contextLits = [l1,l2,cl]() { 
       ASS(l1 < l2) 
       return cl->iterLits()
             .dropNth(l2)
             .dropNth(l1)
             .cloned(); 
    };

    auto mkClause = [&](auto lit1, auto lit2) {
      return Clause::fromIterator(concatIters(
            contextLits(),
            iterItems<Literal*>(lit1,lit2)),
            Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_LITERAL_FACTORING_SIMPL, cl))
          );
    };


    // C \/ t1 + t2 >~ 0 \/ t1 >~ 0
    // =======================
    // C \/ -t2 > 0 \/ t1 + t2 >~ 0
    // C \/  t2 > 0 \/ t1 >~ 0
    //
    //
    // ..............................
    //
    //
    // C \/ t1 + t2 >1 0 \/ t1 >2 0
    // ===================
    // -t2 <  0 -> t1 + t2 > 0
    // -t2 == 0 -> t1 >= 0
    // -t2 >  0 -> t1 >= 0
    // =======================
    //  -t2 ~>1 0 \/ t1 + t2 >1 0
    //   t2 ~>2  0 \/ t1 >2 0

    auto sym1 = *itp1_is_superset ? itp1.symbol() : itp2.symbol();
    auto sym2 = *itp1_is_superset ? itp2.symbol() : itp1.symbol();


    auto t1 = NumTraits::sum(arrayIter(t1s).map([](auto m) { return m.toTerm(); }));
    auto t2 = NumTraits::sum(arrayIter(t2s).map([](auto m) { return m.toTerm(); }));
    if (itp1.symbol() == itp2.symbol()) {

      auto gtsim = [&](auto t) {
        return createLiteral<NumTraits>(itp1.symbol(), t);
      };

      return some(SArray::fromItems(
          // C \/ -t2 > 0 \/ t1 + t2 >~ 0
          mkClause( NumTraits::greater(true, NumTraits::zero(), t2),
                    gtsim(NumTraits::add(t1, t2))),
          // C \/  t2 > 0 \/ t1 >~ 0
          mkClause( NumTraits::greater(true, t2, NumTraits::zero()),
                    gtsim(t1))));

    } else {


      auto gtsim1 = [&](bool b, auto t) { return createLiteral<NumTraits>(b ? sym1 : sym2, t); };

      auto gtsim2 = [&](bool b, auto t) { return gtsim1(!b, t); };

      return some(SArray::fromItems(
      //  -t2 ~>1 0 \/ t1 + t2 >1 0
          mkClause( gtsim1(false, NumTraits::minus(t2)),
                    gtsim1(true, NumTraits::add(t1, t2))),
      //   t2 ~>2  0 \/ t1 >2 0
          mkClause( gtsim2(false, t2),
                    gtsim2(true, t1))));
    }
  }


  template<class NumTraits>
  Option<SArray> apply(Clause* cl,
      unsigned l1, AlascaLiteralItp<NumTraits> const& itp1,
      unsigned l2, AlascaLiteralItp<NumTraits> const& itp2) const 
  {
    if (auto r = applyVariant2(cl,l1,itp1,l2,itp2)) {
      return r;
    } else {
      return applyVariant1(cl,l1,itp1,l2,itp2);
    }
  }

  template<class NumTraits>
  Option<SArray> applyVariant1(Clause* cl,
      unsigned l1, AlascaLiteralItp<NumTraits> const& itp1,
      unsigned l2, AlascaLiteralItp<NumTraits> const& itp2) const 
  {
    if (!itp2.isInequality()) return {};
                
    
    auto contextLits = [l1,l2,cl]() { 
       ASS(l1 < l2) 
       return cl->iterLits()
             .dropNth(l2)
             .dropNth(l1)
             .cloned(); 
    };

    auto mkClause = [&](auto lit1, auto lit2) {
      return Clause::fromIterator(concatIters(
            contextLits(),
            iterItems<Literal*>(lit1,lit2)),
            Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_LITERAL_FACTORING_SIMPL, cl))
          );
    };


    Option<bool> _s_greater_t1;
    for (auto it1 : range(0, itp1.term().nSummands())) {
      auto k1_s = itp1.term().summandAt(it1);
      auto s = k1_s.atom();
      if (k1_s.asNumeral().isNone()) {
        auto foundIt2 = range(0, itp2.term().nSummands())
            .find([&](auto it2) {
              auto k2_s = itp2.term().summandAt(it2); 

              auto rightAtom = itp2.term().summandAt(it2).atom() == s 
                  && k2_s.numeral().sign() == k1_s.numeral().sign();
              if (!rightAtom) return false;
              auto s_greater_t1 = _s_greater_t1.unwrapOrInit([&]() {
                  return _shared->maxSummandIndices(itp1.term(), SelectionCriterion::STRICTLY_MAX)
                    .any([&](auto i) { return i == it1; });
              });
              if (!s_greater_t1) return false;
              auto s_greater_t2 = _shared->maxSummandIndices(itp2.term(), SelectionCriterion::STRICTLY_MAX)
                .any([&](auto i) { return i == it2; });
              return s_greater_t2;
            });
        if (foundIt2) {
          auto it2 = *foundIt2;
          auto k2_s = itp2.term().summandAt(it2); 
          auto pm_s = k1_s.numeral().sign() == Sign::Pos ? s : NumTraits::minus(s);
          auto t1 = NumTraits::linMul(-1 / k1_s.numeral().abs(), NumTraits::sum(itp1.term().iterSummands().dropNth(it1).map([](auto m) { return m.toTerm(); })));
          auto t2 = NumTraits::linMul(-1 / k2_s.numeral().abs(), NumTraits::sum(itp2.term().iterSummands().dropNth(it2).map([](auto m) { return m.toTerm(); })));
          if (itp1.symbol() == itp2.symbol()) {

            auto gtsim = [&](auto l, auto r) {
              return createLiteral<NumTraits>(itp1.symbol(), NumTraits::add(l, NumTraits::minus(r)));
            };
            return some(SArray::fromItems(
                // C \/ t1 > t2 \/ s >1 t1
                mkClause( NumTraits::greater(true, t1, t2),
                          gtsim(pm_s, t1)),
                // C \/ t2 > t1 \/ s >2 t2
                mkClause( NumTraits::greater(true, t2, t1),
                          gtsim(pm_s, t2)) ));
          } else {
            // C \/ s >= t1 \/ s > t2
            // =========================
            // C \/ t1 >  t2 \/ s >= t1
            // C \/ t2 >= t1 \/ s >  t2
            AlascaPredicate p1;
            AlascaPredicate p2;
            if (itp2.symbol() == AlascaPredicate::GREATER_EQ) {
              std::swap(l1, l2);
              std::swap(t1, t2);
              p1 = itp2.symbol();
              p2 = itp1.symbol();
            } else {
              p2 = itp2.symbol();
              p1 = itp1.symbol();
            }
            ASS_EQ(p1, AlascaPredicate::GREATER_EQ)
            ASS_EQ(p2, AlascaPredicate::GREATER)
            return some(SArray::fromItems(
                // C \/ t1 >  t2 \/ s >= t1
                mkClause( NumTraits::greater(true, t1, t2),
                          NumTraits::geq(true, pm_s, t1)),
                // C \/ t2 >= t1 \/ s >  t2
                mkClause( NumTraits::geq(true, t2, t1),
                          NumTraits::greater(true, pm_s, t2) )
                  ));
          }
        }
      }
    }
    return {};
  }

  Option<SArray> apply(Clause* cl, unsigned l1, AlascaLiteralItp<IntTraits> const& itp1) const 
  {
    // TODO think about whether we can make this work
    return {};
  }


  template<class NumTraits>
  Option<SArray> apply(Clause* cl, unsigned l1, AlascaLiteralItp<NumTraits> const& itp1) const 
  {
    if (!itp1.isInequality()) return {};
    for (auto l2 : range(l1 + 1, cl->size())) {
      auto itp2 = InequalityNormalizer::normalize((*cl)[l2]).asItp()
        .flatMap([](auto itp) { return std::move(itp).template as<AlascaLiteralItp<NumTraits>>(); });
      if (itp2.isSome()) {
        if (auto res = apply(cl, l1, itp1, l2, *itp2)) {
          return res;
        }
      }
    }
    return {};
  }


  Option<SArray> apply(Clause* cl, unsigned l1, AlascaLiteralItpAny const& itp1) const 
  { return itp1.apply([=](auto itp1) { return apply(cl, l1, itp1); }); }

  Option<SArray> apply(Clause* cl) const 
  {
    if (cl->size() == 0) {
      return {};
    }
    for (auto l1 : range(0, cl->size() - 1)) {
      if (auto itp1 = InequalityNormalizer::normalize((*cl)[l1]).asItp()) {
        if (auto res = apply(cl, l1, *itp1)) {
          return res;
        }
      }
    }
    return {};
  }
};

#undef DEBUG


} // namespace ALASCA 
} // namespace Inferences 

#endif /*__InequalityFactoring__*/
