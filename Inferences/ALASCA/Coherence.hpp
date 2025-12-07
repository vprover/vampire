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
#include "Kernel/ALASCA/Signature.hpp"
#include "BinInf.hpp"
#include "Lib/STL.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/BacktrackableCollections.hpp"
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
  using SharedSum =  std::shared_ptr<RStack<std::pair<TermList, N>>>;
  static SharedSum toSum(AlascaState& shared, TermList t) {
    RStack<std::pair<TermList, N>> rstack; 
    rstack->loadFromIterator( 
        shared.norm().normalize(t)
          .template wrapPoly<NumTraits>()
          ->iterSummands()
          .map([](auto monom) { return std::make_pair(monom.factors->denormalize(), monom.numeral); }));
    return SharedSum(move_to_heap(std::move(rstack)));
  }
public:

  static const char* name() { return "alasca coherence"; }

  // a clause of the form C \/ ⌊...⌋ = j s + u
  struct Lhs
  {
    ALASCA::SuperpositionConf::Lhs self;
    SharedSum js_u; // <- the them `j s + u`
    unsigned sIdx; // <- the index of `s` in the sum `j s + u`

    auto contextLiterals() const { return self.contextLiterals(); }
    auto rawJ() const { return (**js_u)[sIdx].second; }
    auto s() const { return (**js_u)[sIdx].first; }
    auto j() const { return rawJ().abs(); }
    auto u() const { 
      auto mulByFactor = [&](auto n) { return rawJ().isPositive() ? n : -n;  };
      return ASig::sum(
        range(0, (**js_u).size())
          .filter([&](auto i) { return i != sIdx; })
          .map([&](auto i) -> TermList { return TermList(ASig::linMul(mulByFactor((**js_u)[i].second), (**js_u)[i].first)); })
        ); 
    }
    auto clause() const { return self.clause(); }
    auto asTuple() const { return std::tie(self, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Lhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList((**js_u)[sIdx].first, ASig::sort()); }
    static const char* name() { return "alasca coherence lhs"; }
    static IndexType indexType() { return Indexing::ALASCA_COHERENCE_LHS_SUBST_TREE; }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return iterTraits(ALASCA::Superposition::Lhs::iter(shared, cl))
        .filter([](auto& lhs) -> bool { return ASig::isFloor(lhs.biggerSide()); })
        .filter([](auto& lhs) { return !ASig::isNumeral(lhs.smallerSide()); })
        .map([&shared](auto lhs) {
          auto js_u = toSum(shared, lhs.smallerSide());
          return shared.maxSummandIndices(js_u, SelectionCriterion::NOT_LEQ)
            .map([js_u,lhs](auto sIdx) { return Lhs { lhs, js_u, sIdx }; });
        })
        .flatten()
        .filter([](auto& lhs) { return !lhs.s().isVar(); })
      ;
    }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << "isInt(" << self.j() << TermList(self.key()) << " + " << self.u() << ")"; }
  };

  // a clause of the form D \/ L[⌊k s + t⌋]
  struct Rhs 
  {
    ALASCA::Superposition::Rhs self;
    TermList toRewrite; // <- the term ⌊k s + t⌋
    SharedSum ks_t; // <- the term k s + t
    unsigned sIdx; // <- the index of `s` in the sum `k s + t`

    auto contextLiterals() const { return self.contextLiterals(); }
    auto clause() const { return self.clause(); }
    auto asTuple() const { return std::tie(self, toRewrite, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList((**ks_t)[sIdx].first, ASig::sort()); }
    static const char* name() { return "alasca coherence rhs"; }
    static IndexType indexType() { return Indexing::ALASCA_COHERENCE_RHS_SUBST_TREE; }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return iterTraits(ALASCA::Superposition::Rhs::iter(shared, cl))
        .filterMap([&shared](auto rhs) { 
            auto toRewrite = rhs.key();
            return ASig::ifFloor(toRewrite,
              [&shared, rhs, toRewrite](auto ks_t_term) { 
                auto ks_t = toSum(shared, ks_t_term);
                return range(0, (*ks_t)->size())
                      .map([rhs,ks_t,toRewrite](unsigned sIdx) { return Rhs { rhs, toRewrite, ks_t, sIdx }; })
                      .filter([](auto x) { return !x.key().isVar(); }); 
              }); 
            })
        .flatten();
    }

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << self.self << "@" << self.toRewrite << "@" << TermList(self.key()); }
  };

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
    ASS(j > 0)
    auto k = (**rhs.ks_t)[rhs.sIdx].second;

    auto c = j.denominator().gcd(k.denominator());

    // fx = den(x) / c
    ASS(c.divides(j.denominator()))
    ASS(c.divides(k.denominator()))
    auto fj = j.denominator().intDivide(c);
    auto fk = k.denominator().intDivide(c);

    // v ≡ (num(j)fk)^{−1} mod c
    auto v = (j.numerator() * fk).inverseModulo(c);

    // z = ⌊k (1 - v num(j)fk)/num(j) ⌋
    auto z = (k * (1 - v * j.numerator() * fk) / j.numerator()).floor();

    // i = fj (num(k)v + c z)
    auto i = fj * (k.numerator() * v + c * z);
    DEBUG_COHERENCE(1, "k = ", k)
    DEBUG_COHERENCE(1, "j = ", j)
    DEBUG_COHERENCE(1, "i = ", i)
    DEBUG_COHERENCE(1, "k - i j = ", k - i * j)

    auto sigmaL = [&](auto t) { return uwa.subs().apply(t, lhsVarBank); };
    auto sigmaR = [&](auto t) { return uwa.subs().apply(t, rhsVarBank); };


    auto Lσ         = sigmaR(rhs.self.literal());
    auto toRewriteσ = sigmaR(rhs.toRewrite);
    ASS(rhs.self.literal()->containsSubterm(rhs.toRewrite))
    ASS(Lσ->containsSubterm(toRewriteσ))
    // auto ks_t = rhs.toRewrite.term()->termArg(0);
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
struct CoherenceNormalization : SimplifyingGeneratingInference {
  std::shared_ptr<AlascaState> shared;
  CoherenceNormalization(std::shared_ptr<AlascaState> shared) : shared(std::move(shared)) {}

  void attach(SaturationAlgorithm* salg) final { }

  void detach() final { }

  ClauseGenerationResult generateSimplify(Clause* premise) final {
    return ClauseGenerationResult {
      .clauses = pvi( Superposition::Lhs::iter(*shared, premise)
                        .filter([](auto& x) { return NumTraits::isFloor(x.biggerSide()); })
                        .filterMap([this](auto x) { return apply(std::move(x)); })),
      .premiseRedundant = false,
    };
  }

  // C \/ ⌊s⌋ = t
  // ============ if ⌊t⌋ != ⌊s⌋
  // C \/ ⌊t⌋ = t
  Option<Clause*> apply(Superposition::Lhs prem) const {
    auto floor_s = prem.biggerSide();
    auto t = prem.smallerSide();
    auto floor_t = NumTraits::floor(t);
    if (shared->norm().equivalent(floor_s, floor_t) ) {
      return {};
    } else {
      return some(Clause::fromIterator(
          concatIters(
            prem.contextLiterals(),
            iterItems(NumTraits::eq(true, t, floor_t))
          ),
          Inference(GeneratingInference1(InferenceRule::ALASCA_COHERENCE_NORMALIZATION, prem.clause()))));
    }
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& i) final override { }
#endif
};

#undef DEBUG

} // namespace ALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_Coherence__*/
