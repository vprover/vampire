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
 * @file Coherence.hpp
 * Defines class Coherence
 *
 */

#ifndef __ALASCA_Inferences_Coherence__
#define __ALASCA_Inferences_Coherence__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "BinInf.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/STL.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Reflection.hpp"
#include "Shell/Options.hpp"
#include "Lib/BacktrackableCollections.hpp"
#include "Lib/Output.hpp"
#include "Kernel/EqHelper.hpp"

#define DEBUG_COHERENCE(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class NumTraits>
struct CoherenceConf
{
  using ASig = AlascaSignature<NumTraits>;
  using N = typename NumTraits::ConstantType;
public:
  // TODO do we still need this at all?
  static AlascaTermItp<NumTraits> toSum(AlascaState& shared, TermList t) {
    return shared.norm().normalize(TypedTermList(t, NumTraits::sort()))
      .asSum<NumTraits>().unwrap();
  }

  static const char* name() { return "alasca coherence"; }

  // a clause of the form C \/ ⌊...⌋ = j s + u
  struct Lhs : public ALASCA::SuperpositionConf::Lhs
  {
    AlascaTermItp<NumTraits> js_u; // <- the them `j s + u`
    unsigned sIdx; // <- the index of `s` in the sum `j s + u`

    auto rawJ() const { return js_u[sIdx].numeral(); }
    auto s() const { return js_u[sIdx].atom(); }
    auto j() const { return rawJ().abs(); }
    auto u() const { 
      auto mulByFactor = [&](auto n) { return rawJ().isPositive() ? n : -n;  };
      return ASig::sum(
        js_u.iterSummands()
          .dropNth(sIdx)
          .map([&](auto m) -> TermList { return TermList(ASig::linMul(mulByFactor(m.numeral()), m.atom())); })
        ); 
    }
    auto asTuple() const { return std::tie(static_cast<ALASCA::SuperpositionConf::Lhs const&>(*this), sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Lhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList(s(), ASig::sort()); }
    static std::string name() { return Output::toString("alasca coherence lhs ", NumTraits::name()); }
    static IndexType indexType() { return indexType(NumTraits{}); }
#define FOR_NUM(Num)                                                                      \
    static IndexType indexType(Num ## Traits) { return Indexing::ALASCA_COHERENCE_LHS_SUBST_TREE_ ## Num; }

    FOR_NUM_TRAITS_FRAC_PREFIX(FOR_NUM)
#undef FOR_NUM

    static auto iter(AlascaState& shared, __SelectedLiteral sel) {
      // TODO 4 use selection here and use isInt instead of ⌊..⌋ = t
      // return shared.selectedSummands(cl, /* lit */ SelectionCriterion::NOT_LEQ, /* term */ SelectionCriterion::NOT_LEQ, /*includeUnshieldedNumberVariables=*/ false)
      //   .filter([](auto x) { return is })

      return ALASCA::Superposition::Lhs::iter(shared, sel)
        .filter([](auto& lhs) -> bool { return ASig::isFloor(lhs.biggerSide()); })
        .filter([](auto& lhs) { return !ASig::isNumeral(lhs.smallerSide()); })
        .map([&shared](auto lhs) {
          auto js_u = toSum(shared, lhs.smallerSide());
              // TODO 3 max summands here?
          return shared.maxSummandIndices(js_u, SelectionCriterion::NOT_LEQ)
            .map([lhs, js_u](auto i) { 
                return Lhs { lhs, js_u, i, };
                });
        })
        .flatten()
        .filter([](auto& lhs) { return !lhs.s().isVar(); });
    }

    // static auto iter(AlascaState& shared, SelectedAtom const& sel)
    // {
    //   // TODO 4 use selection here and use isInt instead of ⌊..⌋ = t
    //   // return shared.selectedSummands(cl, /* lit */ SelectionCriterion::NOT_LEQ, /* term */ SelectionCriterion::NOT_LEQ, /*includeUnshieldedNumberVariables=*/ false)
    //   //   .filter([](auto x) { return is })
    //   
    //   return ALASCA::Superposition::Lhs::iter(shared, sel)
    //     .filter([](auto& lhs) -> bool { return ASig::isFloor(lhs.biggerSide()); })
    //     .filter([](auto& lhs) { return !ASig::isNumeral(lhs.smallerSide()); })
    //     .map([&shared](auto lhs) {
    //       auto js_u = toSum(shared, lhs.smallerSide());
    //           // TODO 3 max summands here?
    //       return shared.maxSummandIndices(js_u, SelectionCriterion::NOT_LEQ)
    //         .map([lhs, js_u](auto i) { 
    //             return Lhs { lhs, js_u, i, };
    //             });
    //     })
    //     .flatten()
    //     .filter([](auto& lhs) { return !lhs.s().isVar(); })
    //   ;
    // }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selected(cl, /* literal */ SelectionCriterion::NOT_LEQ, 
                                 /* terms   */ SelectionCriterion::NOT_LEQ,
                                 /* include number vars */ false)
        .flatMap([&shared](auto sel) { return iter(shared, sel); });
    }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << "isInt(" << self.j() << " " << self.s() << " + " << self.u() << ")"; }
  };

  // a clause of the form D \/ L[⌊k s + t⌋]
  struct Rhs : public ALASCA::Superposition::Rhs
  {
    TermList toRewrite; // <- the term ⌊k s + t⌋
    AlascaTermItp<NumTraits> ks_t; // <- the term k s + t
    unsigned sIdx; // <- the index of `s` in the sum `k s + t`

    auto& super() const { return static_cast<ALASCA::SuperpositionConf::Rhs const&>(*this); }
    auto asTuple() const { return std::tie(super(),  /* ks_t redundant */ toRewrite, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList(ks_t[sIdx].atom(), ASig::sort()); }
    static const char* name() { return "alasca coherence rhs"; }
    static IndexType indexType() { return indexType(NumTraits{}); }
#define FOR_NUM(Num)                                                                      \
    static IndexType indexType(Num ## Traits) { return Indexing::ALASCA_COHERENCE_RHS_SUBST_TREE_ ## Num; }

    FOR_NUM_TRAITS_FRAC_PREFIX(FOR_NUM)
#undef FOR_NUM


    static auto iterApplicableSummandsUnderFloor(AlascaState& shared, TermList toRewrite)
    {
      return iterTraits(ASig::ifFloor(toRewrite,
        [&shared](auto ks_t_term) { 
          auto ks_t = toSum(shared, ks_t_term);
          return range(0, ks_t.nSummands())
                .map([ks_t](unsigned sIdx) { return std::make_pair(ks_t, sIdx); })
                .filter([](auto& pair) { 
                    auto& [sum, i] = pair;
                    return !sum[i].atom().isVar(); 
                }); 
        })
        .intoIter()).flatten()
       ; 
    }

    static auto iter(AlascaState& shared, __SelectedLiteral lit) {
      return iterTraits(ALASCA::Superposition::Rhs::iter(shared, lit))
        .flatMap([&shared](auto rhs) { 
            auto toRewrite = rhs.key();
            return iterApplicableSummandsUnderFloor(shared, toRewrite)
              .map([rhs,toRewrite](auto pair) {
                  return Rhs { rhs, toRewrite, pair.first, pair.second, };
                  });
              });
    }

    // static auto iter(AlascaState& shared, SelectedAtom const& atom)
    // {
    //   return iterTraits(ALASCA::Superposition::Rhs::iter(shared, atom))
    //     .flatMap([&shared](auto rhs) { 
    //         auto toRewrite = rhs.key();
    //         return iterApplicableSummandsUnderFloor(shared, toRewrite)
    //           .map([rhs,toRewrite](auto pair) {
    //               return Rhs { rhs, toRewrite, pair.first, pair.second, };
    //               });
    //           });
    // }


    static auto iter(AlascaState& shared, Clause* cl)
    {
      return ALASCA::Superposition::Rhs::activePositions(shared, cl)
        .flatMap([&shared](auto atom) { return iter(shared, atom); });
    }

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << self.super() << "@" << self.toRewrite << "@" << TermList(self.key()); }
  };

  using Numeral = typename NumTraits::ConstantType;
  static Numeral computeI(Numeral j, Numeral k) {
    ASS(j > 0)

    auto c = j.denominator().gcd(k.denominator());

    // fx = den(x) / c
    ASS(c.divides(j.denominator()))
    ASS(c.divides(k.denominator()))
    auto fj = j.denominator().intDivide(c);
    auto fk = k.denominator().intDivide(c);

    // v ≡ (num(j)fk)^{−1} mod c
    auto v = (j.numerator() * fk).inverseModulo(c);

    // z = ⌊k (1 - v num(j)fk)/num(j) ⌋
    auto z = (k * (1 - v * j.numerator() * fk) / Numeral(j.numerator())).floor();

    // i = fj (num(k)v + c z)
    auto i = fj * (k.numerator() * v + c * z);


    DEBUG_COHERENCE(1, "k = ", k)
    DEBUG_COHERENCE(1, "j = ", j)
    DEBUG_COHERENCE(1, "i = ", i)
    DEBUG_COHERENCE(1, "k - i j = ", k - i * j)

    return Numeral(i);
  }

  // lhs: C \/ ⌊...⌋ = j s + u
  // rhs: D \/ L[⌊k s + t⌋]
  // ====================
  // C \/ D \/ L[⌊k s + t - i(j s + u)⌋ + i(j s + u)]
  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  {


    auto j = lhs.j();
    auto k = rhs.ks_t[rhs.sIdx].numeral();
    auto i = computeI(j, k);

    auto sigmaL = [&](auto t) { return uwa.subs().apply(t, lhsVarBank); };
    auto sigmaR = [&](auto t) { return uwa.subs().apply(t, rhsVarBank); };

    auto Lσ         = sigmaR(rhs.literal());
    auto toRewriteσ = sigmaR(rhs.toRewrite);
    ASS(rhs.literal()->containsSubterm(rhs.toRewrite))
    ASS(Lσ->containsSubterm(toRewriteσ))
    auto ks_tσ = toRewriteσ.term()->termArg(0);

    // TODO side condition checks after unification!!

    auto add   = [](auto... as){ return ASig::add(as...); };
    auto floor = [](auto... as){ return ASig::floor(as...); };
    auto mul = [](auto n, auto t){ return ASig::linMul(n, t); };
    auto cnstr = uwa.computeConstraintLiterals();
    auto js_u = add(mul(j, lhs.s()), lhs.u());
    auto js_uσ = sigmaL(js_u);

    return someIf(i != 0, [&]() {
        return Clause::fromIterator(
          concatIters(
            lhs.contextLiterals().map([=](auto l) { return sigmaL(l); }),
            rhs.contextLiterals().map([=](auto l) { return sigmaR(l); }),
            arrayIter(*cnstr).map([](auto& literal) { return literal; }),
            iterItems(EqHelper::replace(Lσ, toRewriteσ, 
                // TermList::var(0)
                add(floor(add(ks_tσ, mul(-i, js_uσ))), mul(i, js_uσ))
            ))
          ), 
          Inference(GeneratingInference2(Kernel::InferenceRule::ALASCA_COHERENCE, lhs.clause(), rhs.clause()))
          );
        }).intoIter();
  }
};

template<class NumTraits>
struct Coherence : public BinInf<CoherenceConf<NumTraits>> {
  Coherence(std::shared_ptr<AlascaState> shared) 
    : BinInf<CoherenceConf<NumTraits>>(shared, {}) 
    {}
};


template<class NumTraits>
struct CoherenceNormalization : public SimplifyingGeneratingInference {
  std::shared_ptr<AlascaState> shared;
  CoherenceNormalization(std::shared_ptr<AlascaState> shared) : shared(std::move(shared)) {}

  void attach(SaturationAlgorithm* salg) final override { }

  void detach() final override { }

  static auto iter(AlascaState& shared, __SelectedLiteral sel) {
    return Superposition::Lhs::iter(shared, sel)
              .filter([](auto& x) { return NumTraits::isFloor(x.biggerSide()); })
              .filter([&shared](auto& prem) {
                auto floor_s = prem.biggerSide();
                auto t = prem.smallerSide();
                auto floor_t = NumTraits::floor(t);
                return !shared.norm().equivalent(floor_s, floor_t);
              });
  }

  ClauseGenerationResult generateSimplify(Clause* premise) final override {
    return ClauseGenerationResult {
      .clauses = pvi( shared->selected(premise, Superposition::Lhs::literalMaximality(), Superposition::Lhs::atomMaximality(), /* unshielded */ false)
                        .flatMap([this](auto x) { return iter(*shared, x); })
                        .map([this](auto x) { return apply(std::move(x)); })),
      .premiseRedundant = false,
    };
  }

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override
  { return pvi(dropElementType(iter(*shared, selection))); }

  // C \/ ⌊s⌋ = t
  // ============ if ⌊t⌋ != ⌊s⌋
  // C \/ ⌊t⌋ = t
  Clause* apply(Superposition::Lhs prem) const {
    auto t = prem.smallerSide();
    auto floor_t = NumTraits::floor(t);
    return Clause::fromIterator(
        concatIters(
          prem.contextLiterals(),
          iterItems(NumTraits::eq(true, t, floor_t))
          ),
        Inference(GeneratingInference1(InferenceRule::ALASCA_COHERENCE_NORMALIZATION, prem.clause())));
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& i) final override { }
#endif
};

#undef DEBUG

} // namespace ALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_Coherence__*/
