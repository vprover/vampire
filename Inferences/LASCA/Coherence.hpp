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

#ifndef __LASCA_Coherence__
#define __LASCA_Coherence__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/LASCA/Superposition.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "BinInf.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Reflection.hpp"
#include "Shell/Options.hpp"
#include "Lib/BacktrackableCollections.hpp"
#include "Debug/Output.hpp"
#include "Kernel/EqHelper.hpp"

#define DEBUG_COHERENCE(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class A, class Iter>
Iter assertIter(Iter iter) {
  static_assert(std::is_same_v<A   ,ELEMENT_TYPE(Iter)> 
             && std::is_same_v<A   , decltype(iter.next())>
             && std::is_same_v<bool, decltype(iter.hasNext())>
             );
  return iter;
}

template<class NumTraits>
struct CoherenceConf
{
  using N = typename NumTraits::ConstantType;
  using SharedSum =  std::shared_ptr<RStack<std::pair<TermList, N>>>;
  static SharedSum toSum(LascaState& shared, TermList t) {
    RStack<std::pair<TermList, N>> rstack; 
    rstack->loadFromIterator( 
        shared.normalize(t)
          .template wrapPoly<NumTraits>()
          ->iterSummands()
          .map([](auto monom) { return std::make_pair(monom.factors->denormalize(), monom.numeral); }));
    return SharedSum(move_to_heap(std::move(rstack)));
  }
public:

  // a clause of the form C \/ ⌊...⌋ = j s + u
  struct Lhs
  {
    LASCA::SuperpositionConf::Lhs self;
    SharedSum js_u; // <- the them `j s + u`
    unsigned sIdx; // <- the index of `s` in the sum `j s + u`

    auto contextLiterals() const { return self.contextLiterals(); }
    auto j() const { return (**js_u)[sIdx].second; }
    auto u() const { return NumTraits::sum(
        range(0, (**js_u).size())
          .filter([&](auto i) { return i != sIdx; })
          .map([&](auto i) -> TermList { return TermList(NumTraits::mul(NumTraits::constantTl((**js_u)[i].second), (**js_u)[i].first)); })
        ); }
    auto clause() const { return self.clause(); }
    auto asTuple() const { return std::tie(self, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Lhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList((**js_u)[sIdx].first, NumTraits::sort()); }
    static const char* name() { return "lasca coherence lhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_LHS_SUBST_TREE; }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Lhs::iter(shared, cl))
        .filter([](auto& lhs) -> bool { return NumTraits::isFloor(lhs.biggerSide()); })
        .map([&shared](auto lhs) {
          auto js_u = toSum(shared, lhs.smallerSide());
          return shared.maxSummandIndices(js_u, SelectionCriterion::NOT_LEQ)
            .map([js_u,lhs](auto sIdx) { return Lhs { lhs, js_u, sIdx }; });
        })
        .flatten()
      ;
    }

    friend std::ostream& operator<<(std::ostream& out, Lhs const& self)
    { return out << self.self << "@" << TermList(self.key()); }
  };

  // a clause of the form D \/ L[⌊k s + t⌋]
  struct Rhs 
  {
    LASCA::Superposition::Rhs self;
    TermList toRewrite; // <- the term ⌊k s + t⌋
    SharedSum ks_t; // <- the term k s + t
    unsigned sIdx; // <- the index of `s` in the sum `k s + t`

    auto contextLiterals() const { return self.contextLiterals(); }
    auto clause() const { return self.clause(); }
    auto asTuple() const { return std::tie(self, toRewrite, sIdx); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs);

    // TODO get rid of the need for a typed term list in this case
    TypedTermList key() const { return TypedTermList((**ks_t)[sIdx].first, NumTraits::sort()); }
    static const char* name() { return "lasca coherence rhs"; }
    static IndexType indexType() { return Indexing::LASCA_COHERENCE_RHS_SUBST_TREE; }

    static auto iter(LascaState& shared, Clause* cl)
    {
      return iterTraits(LASCA::Superposition::Rhs::iter(shared, cl))
        .filterMap([&shared](auto rhs) { 
            auto toRewrite = rhs.key();
            return NumTraits::ifFloor(toRewrite,
              [&shared, rhs, toRewrite](auto ks_t_term) { 
                auto ks_t = toSum(shared, ks_t_term);
                return range(0, (*ks_t)->size())
                      .map([rhs,ks_t,toRewrite](unsigned sIdx) { return Rhs { rhs, toRewrite, ks_t, sIdx }; }); 
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
    auto k = (**rhs.ks_t)[rhs.sIdx].second;

    // c = gcd(den(j), den(k))
    auto c = IntegerConstantType::gcd(j.denominator(), k.denominator());

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
    auto ks_tσ = toRewriteσ.term()->termArg(0);

    // TODO side condition checks after unification!!

    auto js_uσ = sigmaL(lhs.self.smallerSide());
    auto add   = [](auto... as){ return NumTraits::add(as...); };
    auto floor = [](auto... as){ return NumTraits::floor(as...); };
    auto mul = [](auto n, auto t){ return NumTraits::mul(NumTraits::constantTl(n), t); };
    auto cnstr = uwa.computeConstraintLiterals();

    return someIf(i != 0, [&]() {
        return Clause::fromIterator(
          concatIters(
            lhs.contextLiterals().map([=](auto l) { return sigmaL(l); }),
            rhs.contextLiterals().map([=](auto l) { return sigmaR(l); }),
            arrayIter(*cnstr).map([](auto& literal) { return literal; }),
            iterItems(EqHelper::replace(Lσ, toRewriteσ, 
                add(floor(add(ks_tσ, mul(-i, js_uσ))), mul(i, js_uσ))
            ))
          ), 
          Inference(GeneratingInference2(Kernel::InferenceRule::LASCA_COHERENCE, lhs.clause(), rhs.clause()))
          );
        }).intoIter();
  }
};

template<class NumTraits>
struct Coherence : public BinInf<CoherenceConf<NumTraits>> {
  Coherence(std::shared_ptr<LascaState> shared) 
    : BinInf<CoherenceConf<NumTraits>>(shared, {}) 
    {}
};

#undef DEBUG

} // namespace LASCA 
} // namespace Inferences

#endif /*__LASCA_Coherence__*/
