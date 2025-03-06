/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "PolynomialNormalizer.hpp"
#include "Kernel/BottomUpEvaluation.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Kernel {

using namespace std;

/** a struct that normalizes an object of type MonomFactors to a Monom */
struct RenderMonom {

  template<class NumTraits>
  Monom<NumTraits> operator()(PreMonom<NumTraits>&& x) const
  {
    using Monom        = Monom       <NumTraits>;

    auto& factors = *x.factors;
    factors.sort();

    Stack<MonomFactor<NumTraits>> out;

    if (factors.size() > 0) {
      auto cur = MonomFactor<NumTraits>(factors[0], 0);
      for (auto& x : factors) {
        if (x == cur.term) {
          cur.power++;
        } else {
          out.push(cur);
          cur.term = x;
          cur.power = 1;
        }
      }
      out.push(cur);
    }
    return Monom(std::move(x.numeral), perfect(MonomFactors<NumTraits>(std::move(out))));
  };
};

/** a struct that turns any alternative of a NormalizationResult into a PolyNf */
struct RenderPolyNf {

  PolyNf operator()(PolyNf x) const
  { return x; }

  template<class NumTraits>
  PolyNf operator()(Polynom<NumTraits> x) const
  {
    x.raw().sort([](auto& l, auto& r) { return l.factors < r.factors; });
    x.integrity();
    return PolyNf(perfect(std::move(x)));
  }

  template<class NumTraits>
  PolyNf operator()(PreMonom<NumTraits> facs) const
  {
    auto poly = Polynom<NumTraits>(RenderMonom{}(std::move(facs)));
    poly.integrity();
    return (*this)(std::move(poly));
  }


};



template<class NumTraits>
NormalizationResult normalizeAdd(NormalizationResult& lhs, NormalizationResult& rhs) {
  using Polynom = Polynom<NumTraits>;
  using Monom = Monom<NumTraits>;
  using PreMonom = PreMonom<NumTraits>;
  ASS(lhs.is<Polynom>() || lhs.is<PreMonom>())
  ASS(rhs.is<Polynom>() || rhs.is<PreMonom>())

  if (lhs.is<PreMonom>() && rhs.is<Polynom>())  {
    auto& l = lhs.unwrap<PreMonom>();
    auto& r = rhs.unwrap<Polynom>();
    /* Monom(...) + Polynom(x0, x1, ...) ==> Polynom(x0, x1, ..., Monom(...)) */
    r.raw().push(RenderMonom{}(std::move(l)));
    return std::move(rhs);

  } else if (rhs.is<PreMonom>() && lhs.is<Polynom>()){
    auto& r = rhs.unwrap<PreMonom>();
    auto& l = lhs.unwrap<Polynom>();

    /*  Polynom(x0, x1, ...) + Monom(...) ==> Polynom(x0, x1, ..., Monom(...)) */
    l.raw().push(RenderMonom{}(std::move(r)));
    return std::move(lhs);

  } else if (lhs.is<PreMonom>() && rhs.is<PreMonom>()) {
    auto& l = lhs.unwrap<PreMonom>();
    auto& r = rhs.unwrap<PreMonom>();

    /* Monom(x0, x1, ...) + Monom(y0, y1, ...) ==> Polynom(Monom(x0, x1, ...), Polynom(y0, y1, ...)) */
    Stack<Monom> summands(2);
    summands.push(RenderMonom{}(std::move(l)));
    summands.push(RenderMonom{}(std::move(r)));
    return NormalizationResult(Polynom(std::move(summands)));

  } else{
    ASS(lhs.is<Polynom>())
    ASS(rhs.is<Polynom>())
    auto& l = lhs.unwrap<Polynom>();
    auto& r = rhs.unwrap<Polynom>();

    /* Polynom(x0, x1, ...) + Polynom(y0, y1, ...) ==> Polynom(x0, x1, ..., y0, y1, ...) */
    l.raw().reserve(l.raw().size() + r.raw().size());
    l.raw().loadFromIterator(r.raw().iter());
    return std::move(lhs);
  }
}


template<class NumTraits>
NormalizationResult normalizeMul(NormalizationResult& lhs, NormalizationResult& rhs, bool& simplified) {
  using Polynom      = Polynom<NumTraits>;
  using PreMonom     = PreMonom<NumTraits>;
  ASS(lhs.is<Polynom>() || lhs.is<PreMonom>())
  ASS(rhs.is<Polynom>() || rhs.is<PreMonom>())

  if (lhs.is<PreMonom>() && rhs.is<Polynom>())  {
    auto& l = lhs.unwrap<PreMonom>();
    auto& r = rhs.unwrap<Polynom>();
    /* Monom(x0, x1, ...) * Polynom(...) ==> Monom(x0, x1, ..., Polynom(...)) */
    l.factors->push(RenderPolyNf{}(std::move(r)));
    return std::move(lhs);

    // rhs.raw().push(toNormalizedMonom(std::move(lhs)));
    // return std::move(rhs);

  } else if (rhs.is<PreMonom>() && lhs.is<Polynom>()){
    auto& r = rhs.unwrap<PreMonom>();
    auto& l = lhs.unwrap<Polynom>();
    /* Polynom(...) * Monom(x0, x1, ...) ==> Monom(x0, x1, ..., Polynom(...)) */
    r.factors->push(RenderPolyNf{}(std::move(l)));
    return std::move(rhs);

    // lhs.raw().push(toNormalizedMonom(std::move(rhs)));
    // return std::move(lhs);

  } else if (lhs.is<PreMonom>() && rhs.is<PreMonom>()) {
    auto& l = lhs.unwrap<PreMonom>();
    auto& r = rhs.unwrap<PreMonom>();

    /* Monom(x0, x1, ...) * Monom(y0, y1, ...) ==> Monom(x0, x1, ..., y0, y1, ...) */
    l.factors->reserve(l.factors->size() + r.factors->size());
    l.factors->loadFromIterator(r.factors->iter());
    if (l.numeral != 1 && r.numeral != 1) {
      simplified = true;
    }
    l.numeral *= r.numeral;
    return std::move(lhs);

  } else{
    ASS(lhs.is<Polynom>())
    ASS(rhs.is<Polynom>())
    auto l = RenderPolyNf{}(std::move(lhs.unwrap<Polynom>()));
    auto r = RenderPolyNf{}(std::move(rhs.unwrap<Polynom>()));

    /* Polynom(x0, x1, ...) * Polynom(y0, y1, ...) ==> Monom(Polynom(x0, x1, ...), Polynom(y0, y1, ...)) */

    return NormalizationResult(PreMonom({ l, r }));
  }
}
template<class NumTraits>
Option<NormalizationResult> normalizeSpecialized(Interpretation i, NormalizationResult* ts, bool& simplified);

template<class NumTraits>
Option<NormalizationResult> normalizeDiv(NormalizationResult& lhs, NormalizationResult& rhs, bool& simplified);

template<class NumTraits>
Option<NormalizationResult> normalizeSpecializedFractional(Interpretation i, NormalizationResult* ts, bool& simplified)
{
  switch (i) {
    case NumTraits::divI:
      ASS(ts != nullptr);
      return normalizeDiv<NumTraits>(ts[0], ts[1], simplified);
    default:
      return Option<NormalizationResult>();
  }
}


template<>
Option<NormalizationResult> normalizeSpecialized<IntTraits>(Interpretation i, NormalizationResult* ts, bool& simplified) 
{ return Option<NormalizationResult>(); }

template<>
Option<NormalizationResult> normalizeSpecialized<RatTraits>(Interpretation i, NormalizationResult* ts, bool& simplified) 
{ return normalizeSpecializedFractional< RatTraits>(i,ts,simplified); }

template<>
Option<NormalizationResult> normalizeSpecialized<RealTraits>(Interpretation i, NormalizationResult* ts, bool& simplified) 
{ return normalizeSpecializedFractional<RealTraits>(i,ts,simplified); }

template<class NumTraits>
struct TryNumeral {
  using Numeral = typename NumTraits::ConstantType;

  Option<Numeral const&> operator()(PolyNf& term) const
  { ASSERTION_VIOLATION }

  Option<Numeral const&> operator()(Polynom<NumTraits> const& term) const
  {
    ASS(term.nSummands() > 1)
    return {};
  }

  Option<Numeral const&> operator()(PreMonom<NumTraits> const& term) const
  {
    if (term.factors->size() == 0) {
      return Option<Numeral const&>(term.numeral);
    } else {
      return {};
    }
  }

  template<class Num2>
  Option<Numeral const&> operator()(PreMonom<Num2> const& term) const
  {
    static_assert(!std::is_same_v<Num2,NumTraits>);
    ASSERTION_VIOLATION
  }

  template<class Num2>
  Option<Numeral const&> operator()(Polynom<Num2> const& term) const
  {
    static_assert(!std::is_same_v<Num2,NumTraits>);
    ASSERTION_VIOLATION
  }

  // template<class C> Option<Numeral> operator()(C& term) const
  // { return Option<Numeral>(); }


};

template<class ConstantType>
NormalizationResult wrapNumeral(ConstantType c)
{
  using NumTraits = NumTraits<ConstantType>;
  return NormalizationResult(PreMonom<NumTraits>(std::move(c)));
}

template<class NumTraits>
Option<NormalizationResult> normalizeDiv(NormalizationResult& lhs, NormalizationResult& rhs, bool& simplfied) {
  auto num = rhs.apply(TryNumeral<NumTraits>{});
  if (num.isSome() && *num != 0 ) {
    auto inv = wrapNumeral(1 / *num);
    return Option<NormalizationResult>(normalizeMul<NumTraits>(inv, lhs, simplfied));
  } else {
    return Option<NormalizationResult>();
  }
}


template<class NumTraits>
NormalizationResult normalizeMinus(NormalizationResult& x, bool& simplified) {
  using Numeral = typename NumTraits::ConstantType;

  auto minusOne = wrapNumeral(Numeral(-1));
  return normalizeMul<NumTraits>(minusOne, x, simplified);
}

template<class NumTraits>
NormalizationResult normalizeNumSort(TermList t, NormalizationResult* ts, bool& simplified)
{
  using Polynom      = Polynom<NumTraits>;
  using PreMonom     = PreMonom    <NumTraits>;

  auto singletonProduct = [](PolyNf t) -> NormalizationResult {
    return NormalizationResult(PreMonom({t}));
  };

  if (t.isVar()) {
    return singletonProduct(PolyNf(Variable(t.var())));

  } else {
    auto term = t.term();
    auto res = NumTraits::ifLinMul(term, [&](auto& n, auto t) -> NormalizationResult {
        auto& inner = ts[0];
        ASS(inner.is<Polynom>() || inner.is<PreMonom>())
        if (inner.is<Polynom>()) {
          return NormalizationResult(
              PreMonom(n, {RenderPolyNf{}(std::move(*inner.template as<Polynom>()))}));
        } else {
          if (inner.as<PreMonom>()->numeral != 1 && n != 1) {
            simplified = true;
          }
          inner.as<PreMonom>()->numeral *= n;
          return std::move(inner);
        }
    });
    if (res) return std::move(*res);
    if (auto n = NumTraits::tryNumeral(term)) {
      return wrapNumeral(*n);
    }
    auto fn = FuncId::symbolOf(term);
    if (fn.isInterpreted()) {
      switch(fn.interpretation()) {
        case NumTraits::mulI:
          ASS(ts != nullptr);
          return normalizeMul<NumTraits>(ts[0], ts[1], simplified);
        case NumTraits::addI:
          ASS(ts != nullptr);
          return normalizeAdd<NumTraits>(ts[0], ts[1]);
        case NumTraits::binMinusI:{
          ASS(ts != nullptr);
          auto rhs = normalizeMinus<NumTraits>(ts[1], simplified);
          return normalizeAdd<NumTraits>(ts[0], rhs);
        }
        case NumTraits::minusI:
          ASS(ts != nullptr);
          return normalizeMinus<NumTraits>(ts[0], simplified);
        default:
        {
          auto out = normalizeSpecialized<NumTraits>(fn.interpretation(), ts, simplified);
          if (out.isSome()) {
            return std::move(out.unwrap());
          }
        }
      }
    }

    return singletonProduct(PolyNf(perfect(FuncTerm(
        fn, 
        Stack<PolyNf>::fromIterator(
            arrayIter(ts, fn.numTermArguments())
            .map( [](NormalizationResult& r) -> PolyNf { return std::move(r).apply(RenderPolyNf{}); }))
      )
    )));
  }
}

PolyNf normalizeTerm(TypedTermList t, bool& simplified)
{
  DBG_INDENT
  DEBUG(0, "normalizing ", t)
  static MemoNonVars<TypedTermList, std::pair<PolyNf, bool>> memo;
  auto out = memo.getOrInit(t, [&t]() {

      bool simplified = false;
  NormalizationResult r = BottomUpEvaluation<TypedTermList, NormalizationResult>()
    .function(
        [&](TypedTermList t, NormalizationResult* ts) -> NormalizationResult 
        { 
          auto sort = t.sort();
          if (sort ==  IntTraits::sort()) { return normalizeNumSort< IntTraits>(t, ts, simplified); }
          if (sort ==  RatTraits::sort()) { return normalizeNumSort< RatTraits>(t, ts, simplified); }
          if (sort == RealTraits::sort()) { return normalizeNumSort<RealTraits>(t, ts, simplified); }
          else {
            if (t.isVar()) {
              return NormalizationResult(PolyNf(Variable(t.var())));
            } else {
              auto fn = FuncId::symbolOf(t.term());
              return NormalizationResult(PolyNf(perfect(FuncTerm(
                  fn, 
                  Stack<PolyNf>::fromIterator(
                      iterTraits(arrayIter(ts, fn.numTermArguments()))
                      .map( [](NormalizationResult& r) -> PolyNf { return std::move(r).apply(RenderPolyNf{}); }))
                )
              )));
            }
          }
        })
    .apply(t);

  DEBUG(1, "normed: ", r)
  auto out = std::move(r).apply(RenderPolyNf{});
  DEBUG(0, "out: ", out)
  return std::make_pair(out, simplified);
  });
  simplified = out.second;
  DEBUG(0, "normed: ", t, " ==> ", out)
  return out.first;
}

TermList PolyNf::denormalize() const
{ 
  static MemoNonVars<PolyNf, TermList> memo;
  return BottomUpEvaluation<PolyNf, TermList>()
    .function(
        [&](PolyNf orig, TermList* results) -> TermList
        { return orig.match(
            [&](Perfect<FuncTerm> t) { 
            return TermList(Term::createFromIter(t->function().id(), 
                concatIters(
                  t->function().iterTypeArgs(),
                  range(0, t->numTermArguments()).map([&](auto i){ return results[i]; })
                ))); },
            [&](Variable          v) { return TermList::var(v.id()); },
            [&](AnyPoly           p) { return p.denormalize(results); }
            ); })
    .memo<decltype(memo)&>(memo)
    .apply(*this);
}



} // namespace Kernel
