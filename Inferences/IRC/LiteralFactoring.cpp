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
 * @file LiteralFactoring.cpp
 * Defines class LiteralFactoring
 *
 */

#include "LiteralFactoring.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

void LiteralFactoring::attach(SaturationAlgorithm* salg) 
{ }

void LiteralFactoring::detach() 
{ }

//  C \/ ±js1 + t1 <> 0 \/ ±ks2 + t2 <> 0
// ====================================================
// (C \/ ±js1 + t1 <> 0 \/ k t1 − j t2  ̸≈ 0) σ \/ Cnst
//
//
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • <> ∈ {>,≥,≈, /≈}
// • s1σ /⪯ terms(t1)σ
// • s2σ /⪯ terms(t2)σ
// • (±ks1 + t1 <> 0)σ /< (±ks2 + t2 <> 0 \/ C)σ
// • (±ks2 + t2 <> 0)σ /< (±ks1 + t1 <> 0 \/ C)σ


template<class NumTraits>
Option<Clause*> LiteralFactoring::applyRule(Clause* premise, 
    Literal* lit1, IrcLiteral<NumTraits> l1,  Monom<NumTraits> j_s1,
    //       ^^^^--> `±js1 + t1 <> 0` <--^^            ±js1 <--^^^^
    Literal* lit2, IrcLiteral<NumTraits> l2,  Monom<NumTraits> k_s2,
    //       ^^^^--> `±ks2 + t2 <> 0` <--^^            ±ks2 <--^^^^
    UwaResult uwa)
{

  auto nothing = []() { return Option<Clause*>(); };
  auto sigma = [&](auto x){ return uwa.sigma.apply(x, /* varbank */ 0); };
  auto& cnst  = uwa.cnst;
  auto j = j_s1.numeral;
  auto k = k_s2.numeral;
  auto s1 = j_s1.factors;
  auto s2 = k_s2.factors;
  if(j.isPositive() != k.isPositive()
     || l1.symbol() != l2.symbol())
    return nothing();

  auto term_max_after_unif = [&sigma, this](auto lit_sigma, auto s) -> bool
  {
      auto lit_sigma_norm = _shared->renormalize<NumTraits>(lit_sigma);
      if (lit_sigma_norm.isNone())  
        return true; // overflow while normalizing, we assume that we can apply the rule
      auto strictly_max = _shared->maxAtomicTerms(lit_sigma_norm.unwrap(), /*strict*/true);
      auto s_sigma = _shared->normalize(TypedTermList(sigma(s->denormalize()).term())).wrapMonom<NumTraits>();
      if (iterTraits(strictly_max.iterFifo()).all([&](auto monom) { return monom.factors != s_sigma.factors; }))
        return false;
      else 
        return true;
  };

  // checking s1σ /⪯ terms(t1)σ
  auto lit1_sigma = sigma(lit1);
  if (!term_max_after_unif(lit1_sigma, s1))
    return nothing();

  // checking s2σ /⪯ terms(t2)σ
  auto lit2_sigma = sigma(lit2);
  if (!term_max_after_unif(lit2_sigma, s2))
    return nothing();

  {
    auto premLits = iterTraits(premise->iterLits()).template collect<Stack>();
    auto maxLiterals = _shared->maxLiterals(sigma(std::move(premLits)));

    // checking (±ks1 + t1 <> 0)σ /< (±ks2 + t2 <> 0 \/ C)σ
    if (!iterTraits(maxLiterals.iterFifo()).any([&](auto x) { return x == lit1_sigma; }))
      return nothing();

    // checking (±ks2 + t2 <> 0)σ /< (±ks1 + t1 <> 0 \/ C)σ
    if (!iterTraits(maxLiterals.iterFifo()).any([&](auto x) { return x == lit2_sigma; }))
      return nothing();
  }


  Stack<Literal*> conclusion(premise->size() + cnst.size());

  // adding `(C \/ ±js1 + t1 <> 0)σ`
  { 
    auto lit2cnt = 0;
    for (auto lit : iterTraits(premise->getLiteralIterator())) {
      if (lit == lit2) {
        lit2cnt++;
      } else if (lit == lit1) {
        conclusion.push(lit1_sigma);
      } else {
        ASS(lit != lit2)
        conclusion.push(sigma(lit));
      }
    }
    if (lit2cnt > 1) {
      conclusion.push(lit2_sigma);
    }
  }

  auto pivotSum = 
  //   ^^^^^^^^--> `k t1 − j t2`
    NumTraits::sum(iterTraits(getConcatenatedIterator(
      l1.term().iterSummands()
        .filter([&](auto t) { return t != j_s1; })
        .map([&](auto t) { return  (k * t).denormalize(); }),

      l2.term().iterSummands()
        .filter([&](auto t) { return t != k_s2; })
        .map([&](auto t) { return  (-j * t).denormalize(); })
        )));
  auto pivotLiteral = NumTraits::eq(false, pivotSum, NumTraits::zero());

  // adding `(k t1 − j t2  ̸≈ 0)σ`
  conclusion.push(sigma(pivotLiteral));

  // adding `Cnst`
  conclusion.loadFromIterator(uwa.cnstLiterals());

  Inference inf(GeneratingInference1(Kernel::InferenceRule::IRC_LITERAL_FACTORING, premise));

  env.statistics->ircLitFacCnt++;
  return some(Clause::fromStack(conclusion, inf));
}


template<template<class> class Obj> class AllNumTraits;
template<class NumTraits, template<class> class Obj2> struct __getAllNumTraits {
  Obj2<NumTraits>     & operator()(AllNumTraits<Obj2>      &);
  Obj2<NumTraits>const& operator()(AllNumTraits<Obj2> const&);
};

template<template<class> class Obj>
class AllNumTraits {
  Obj< IntTraits> _int;
  Obj< RatTraits> _rat;
  Obj<RealTraits> _real;
public:
  AllNumTraits( Obj< IntTraits> intObj, Obj< RatTraits> ratObj, Obj<RealTraits> realObj)
   : _int(std::move(intObj))
   , _rat(std::move(ratObj))
   , _real(std::move(realObj)) 
  {}


  template<class NumTraits, template<class> class Obj2> friend struct __getAllNumTraits;

  template<class NumTraits> Obj<NumTraits>      & get()       { return __getAllNumTraits<NumTraits, Obj>{}(*this); }
  template<class NumTraits> Obj<NumTraits> const& get() const { return __getAllNumTraits<NumTraits, Obj>{}(*this); }
private:
  Obj< IntTraits> const&  getInt() const { return _int;  }
  Obj< RatTraits> const&  getRat() const { return _rat;  }
  Obj<RealTraits> const& getReal() const { return _real; }

  Obj< IntTraits>&  getInt() { return _int;  }
  Obj< RatTraits>&  getRat() { return _rat;  }
  Obj<RealTraits>& getReal() { return _real; }
};


template<template<class> class Obj> 
struct __getAllNumTraits< IntTraits, Obj> {
  Obj< IntTraits>     & operator()(AllNumTraits<Obj>      & self) { return self. getInt(); }
  Obj< IntTraits>const& operator()(AllNumTraits<Obj> const& self) { return self. getInt(); }
};

template<template<class> class Obj> 
struct __getAllNumTraits< RatTraits, Obj> {
  Obj< RatTraits>     & operator()(AllNumTraits<Obj>      & self) { return self. getRat(); }
  Obj< RatTraits>const& operator()(AllNumTraits<Obj> const& self) { return self. getRat(); }
};


template<template<class> class Obj> 
struct __getAllNumTraits<RealTraits, Obj> {
  Obj<RealTraits>     & operator()(AllNumTraits<Obj>      & self) { return self.getReal(); }
  Obj<RealTraits>const& operator()(AllNumTraits<Obj> const& self) { return self.getReal(); }
};


  template<class NumTraits> using MaxTermStack = Stack<MaxAtomicTerm<NumTraits>>;
  template<class NumTraits> using SharedMaxTermStack = shared_ptr<MaxTermStack<NumTraits>>;

auto range(unsigned from, unsigned to) { return iterTraits(getRangeIterator(from, to)); }

template<class NumTraits>
ClauseIterator LiteralFactoring::generateClauses(Clause* premise, 
    Literal* lit1, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, IrcLiteral<NumTraits> l2, Monom<NumTraits> k_s2) 
{

    auto s1 = j_s1.factors->denormalize();
    auto s2 = k_s2.factors->denormalize();
    return pvi(iterTraits(_shared->unify(s1, s2)
      .andThen([&](auto sigma_cnst){ return applyRule(premise, lit1, l1, j_s1, 
                                                           lit2, l2, k_s2, 
                                                           std::move(sigma_cnst)); })
      .intoIter()));


}

template<class NumTraits>
ClauseIterator LiteralFactoring::generateClauses(
    Clause* premise,
    Literal* lit1, IrcLiteral<NumTraits> L1,
    Literal* lit2, IrcLiteral<NumTraits> L2
  ) 
{
  auto maxAtomic = [this](auto L) { return make_shared(new Stack<Monom<NumTraits>>(_shared->maxAtomicTerms(L, /* strict = */ true))); };
  auto max1 = maxAtomic(L1);
  auto max2 = maxAtomic(L2);
  return pvi(range(0, max1->size())
    .flatMap([=](auto i) {
      return pvi(range(0, max2->size())
        .flatMap([=](auto j) {
          auto k_s1 = (*max1)[i];
          auto j_s2 = (*max2)[j];
          return generateClauses(premise, lit1, L1, k_s1, lit2, L2, j_s2);
        }));
    }));
}

template<class A>
A* move_to_heap(A&& a) 
{ return new A(std::move(a)); }

ClauseIterator LiteralFactoring::generateClauses(Clause* premise) 
{

  DEBUG("in: ", *premise)

  auto selected = make_shared(move_to_heap(_shared->maxLiterals(premise)));
  return pvi(
      range(0, selected->size())
        .flatMap([=](unsigned i) {
          auto lit1 = (*selected)[i];
          auto L1_opt = _shared->renormalize(lit1);
          return pvi(iterTraits(std::move(L1_opt).intoIter())
            .flatMap([=](auto polymorphicNormalized) {
                // we know that the first literal is an inequality of some number sort
                // we dispatch on the number sort
                return polymorphicNormalized.apply([&](auto L1) {
                      using NumTraits = typename decltype(L1)::NumTraits;
                      return pvi(range(i + 1, selected->size())
                        .flatMap([=](auto j) {
                          auto lit2 = (*selected)[j];
                          // we check whether the second is an inequality literal of the same number sort
                          auto L2_opt = _shared->renormalize<NumTraits>(lit2);
                          auto ci = pvi(iterTraits(std::move(L2_opt).intoIter())
                            .flatMap([&](IrcLiteral<NumTraits> L2) 
                                { return generateClauses(premise, lit1, L1, lit2, L2); }));
                          return ci;

                        }));

                  });
            }));
          })
    );
}

  

#if VDEBUG
void LiteralFactoring::setTestIndices(Stack<Indexing::Index*> const&) 
{

}
#endif

} // namespace IRC 
} // namespace Inferences 
