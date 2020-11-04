
#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__

#include "Lib/Int.hpp"
#include "Forwards.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/UniqueShared.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Optional.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"
#include "Inferences/InferenceEngine.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Kernel {
using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;

template<class Number> class Sum;

template<class Number>
class Prod 
{ 
  friend class Sum<Number>;
  Stack<PolyNf> _factors; 
public:
  template<class... Fs>
  explicit Prod(Fs... factors) : _factors(Stack<PolyNf>{factors...}) { }
  Prod(Prod&&) = default;
  Prod& operator=(Prod&&) = default;

  friend ostream& operator<<(ostream& out, Prod const& self) 
   { return out << "Prod" << self._factors; }
};


using NormalizationResult = Coproduct<PolyNf 
        , Sum< IntTraits>
        , Sum< RatTraits>
        , Sum<RealTraits>
        >;

PolyNf toPolyNf(NormalizationResult& r);

template<class Number>
class Sum 
{ 
  using Const = typename Number::ConstantType;
  using Prod = Kernel::Prod<Number>;
  Stack<Prod> _summands; 

  explicit Sum(Prod&& m0, Prod&& m1) : _summands(Stack<Prod>(2)) 
  {
    _summands.push(std::move(m0));
    _summands.push(std::move(m1));
  }

public:

  explicit Sum(Prod&& m0) : _summands(Stack<Prod>(1)) 
  { _summands.push(std::move(m0)); }

  Sum(Sum&&) = default;
  Sum& operator=(Sum&&) = default;

  static NormalizationResult mul(PolyNf& t, Sum& p)
  {
    if (p._summands.size() == 1) {
      //  Poly(Mon(p0 * p1 * ... )) * t ==> Poly(Mon(t * p0 * ... ))
      p._summands[0]._factors.push(std::move(t));
      return NormalizationResult(std::move(p));
    } else {
      ASS(p._summands.size() > 1);
      //  Poly(p0 + p1 + ...) * t ==> Poly(Mon(t * Poly(p0 + p1 + ...)))
      return NormalizationResult(Sum( Prod ( t, p.polyNf() ) ));
    }
  }

  static NormalizationResult mul(Sum& lhs, Sum& rhs)
  {
    ASS_NEQ(lhs._summands.size(), 0)
    ASS_NEQ(rhs._summands.size(), 0)

    if (lhs._summands.size() == 1 && rhs._summands.size() == 1) {
      //  Poly(Mon(l0 * l1 * ... )) * Poly(Mon(r0 * r1 * ...)) ==> Poly(Mon(l0 * ... * r0 * ...))
      lhs._summands[0]._factors.moveFromIterator(rhs._summands[0]._factors.iter());
      return NormalizationResult(std::move(lhs));
    } else if (lhs._summands.size() > 1 && rhs._summands.size() == 1) {
      //               Poly(l0 + l1 + ...) * Poly(Mon(r0 * r1 * ...)) 
      //  ==> Poly(Mon(Poly(l0 + l1 + ...) *          r0 * r1 * ...))
      rhs._summands[0]._factors.push(lhs.polyNf());
      return NormalizationResult(std::move(rhs));
    } else if (lhs._summands.size() == 1 && rhs._summands.size() > 1) {
      // symmetric to the last case
      lhs._summands[0]._factors.push(rhs.polyNf());
      return NormalizationResult(std::move(lhs));

    } else if (lhs._summands.size() > 1 && rhs._summands.size() > 1) {
      //               Poly(l0 + l1 + ...) * Poly(r0 + r1 + ...)
      //  ==> Poly(Mon(Poly(l0 + l1 + ...) * Poly(r0 + r1 + ...))
      return NormalizationResult(Sum( Prod(lhs.polyNf(), rhs.polyNf()) ));
    }
    ASSERTION_VIOLATION
  }


  static NormalizationResult mul(NormalizationResult& lhs, NormalizationResult& rhs)
  {
    if (lhs.is<PolyNf>() && rhs.is<PolyNf>()) {
      return NormalizationResult(Sum ( 
          Prod(
              lhs.unwrap<PolyNf>(), 
              rhs.unwrap<PolyNf>() 
          )
        ));
    } else if (lhs.is<PolyNf>() && rhs.is<Sum>()) {
      return mul(lhs.unwrap<PolyNf>(), rhs.unwrap<Sum>());
    } 
    ASS(lhs.is<Sum>());
    if (rhs.is<PolyNf>()) {
      return mul(rhs.unwrap<PolyNf>(), lhs.unwrap<Sum>());
    }  else {
      return mul(lhs.unwrap<Sum>(), rhs.unwrap<Sum>());
    }
  }

  Optional<typename Number::ConstantType> tryNumeral() const
  {
    if (_summands.size() == 1 && _summands[0]._factors.size() == 1) {
      return _summands[0]._factors[0].template tryNumeral<Number>();
    } else {
      return Optional<typename Number::ConstantType>();
    }
  }

  static NormalizationResult numeral(PolyNf p) 
  { return NormalizationResult(Sum(Prod(p))); }

  static NormalizationResult numeral(typename Number::ConstantType c) 
  { 
    auto fun = FuncId(theory->representConstant(c)->functor());
    return numeral(PolyNf(unique(FuncTerm(fun, Stack<PolyNf>{}))));
  }

  static NormalizationResult add(NormalizationResult& lhs, NormalizationResult& rhs)
  {
    if (lhs.is<PolyNf>() && rhs.is<PolyNf>()) {
      return NormalizationResult(Sum(Prod(lhs.unwrap<PolyNf>()), Prod(rhs.unwrap<PolyNf>())));
    } else if (lhs.is<PolyNf>() || rhs.is<PolyNf>()) {
      Sum p = rhs.is<PolyNf>() ? std::move(lhs).unwrap<Sum>() : std::move(rhs).unwrap<Sum>();
      PolyNf  t = rhs.is<PolyNf>() ? rhs.unwrap< PolyNf>() : lhs.unwrap< PolyNf>();
      p._summands.push(Prod(t));
      return NormalizationResult(std::move(p));
    } else {
      ASS(lhs.is<Sum>())
      ASS(rhs.is<Sum>())
      auto out = std::move(lhs).unwrap<Sum>();
      out._summands.moveFromIterator(rhs.unwrap<Sum>()._summands.iter());
      return NormalizationResult(std::move(out));
    }
  }

  PolyNf polyNf()  
  {
    using Monom        = Kernel::Monom<Number>;
    using Polynom      = Kernel::Polynom  <Number>;
    using MonomFactor  = Kernel::MonomFactor <Number>;
    using MonomFactors = Kernel::MonomFactors<Number>;

    // auto begin = _summands.begin();
    auto summands = 
        // iterTraits(_summands.iter())
        iterTraits(getArrayishObjectIterator<mut_ref_t>(_summands))
          .map([](Prod& p) -> Monom {
            std::sort(p._factors.begin(), p._factors.end()); // TODO make different orderings possible
            Stack<MonomFactor> monomFactors;
            auto iter = p._factors.begin();
            Optional<Const> coeff;
            while (iter != p._factors.end()) {
              auto elem = *iter;
              auto num = elem.template tryNumeral<Number>();
              if (num.isSome() && coeff.isNone()) {
                 coeff = some(num.unwrap());
                 iter++;
              } else {
                unsigned cnt = 0;
                while (iter != p._factors.end() && *iter == elem) {
                  cnt++;
                  iter++;
                }
                ASS(cnt != 0);
                monomFactors.push(MonomFactor(elem, cnt));
              }
            }
            return Monom(coeff.unwrapOr(Const(1)), unique(MonomFactors(std::move(monomFactors))));
          })
          .template collect<Stack>();
    auto sbegin = summands.begin();
    auto send = summands.end();
    std::sort(sbegin, send); 

    // TODO insert into memo
    return PolyNf(AnyPoly(unique(Polynom(std::move(summands)))));
  }

  static NormalizationResult minus(NormalizationResult& inner)
  { 
    static NormalizationResult minusOne(PolyNf(unique(FuncTerm(FuncId(Number::constantT(-1)->functor()), nullptr))));
    return mul(minusOne, inner); 
  }

public:
  friend ostream& operator<<(ostream& out, Sum const& self) 
  { return out << "Sum" << self._summands; }
};

inline PolyNf toPolyNf(NormalizationResult& r) {
    return std::move(r).match(
        [](PolyNf  x)             { return x; },
        // TODO insert into memo after conversion
        [](Sum< IntTraits>&& x) { return x.polyNf(); }, 
        [](Sum< RatTraits>&& x) { return x.polyNf(); },
        [](Sum<RealTraits>&& x) { return x.polyNf(); }
      );
}

class NormalizationMemo 
{

  Map<TermList, PolyNf> _cache;

public:
  Optional<NormalizationResult> get(TermList t) 
  { return optionalFromPtr(_cache.getPtr(t))
              .map([](PolyNf&& p) 
                   { return NormalizationResult(p); }); }

  template<class Init>
  NormalizationResult getOrInit(TermList const& t, Init init) 
  { // TODO don't hash twice
    auto entry = optionalFromPtr(_cache.getPtr(t));
    if (entry.isSome()) {
      return NormalizationResult(entry.unwrap());
    } else {
      auto out = init();
      if (out.template is<PolyNf>()) {
        insert(t, out.template unwrap<PolyNf>());
      }
      return std::move(out);
    }
  }

  void insert(TermList const& t, PolyNf const& p)
  { 
    _cache.insert(t, p); 
    // DEBUG(_cache.numberOfElements());
  }
};

inline PolyNf normalizeTerm(TypedTermList t) 
{
  CALL("PolyNf::normalize")
  DEBUG("normalizing ", t)
  NormalizationMemo memo;
  struct Eval 
  {
    using Arg    = TypedTermList;
    using Result = NormalizationResult;

    Optional<NormalizationResult> normalizeInterpreted(Interpretation i, NormalizationResult* results) const
    {
      switch (i) {
#     define NUM_CASE(NumTraits)                                                                              \
        case NumTraits::mulI:                                                                                 \
          return some<NormalizationResult>(Sum<NumTraits>::mul(results[0], results[1]));                      \
        case NumTraits::addI:                                                                                 \
          return some<NormalizationResult>(Sum<NumTraits>::add(results[0], results[1]));                      \
        case NumTraits::minusI:                                                                               \
          return some<NormalizationResult>(Sum<NumTraits>::minus(results[0]));

#     define FRAC_CASE(NumTraits)                                                                             \
        case NumTraits::divI:                                                                                 \
        {                                                                                                     \
          auto maybeNumeral = results[1].template as<Sum<NumTraits>>()                                        \
            .andThen([](Sum<NumTraits> const& p)                                                              \
                { return p.tryNumeral(); });                                                                  \
                                                                                                              \
          return maybeNumeral                                                                                 \
            .andThen([&](NumTraits::ConstantType& c)->Optional<NormalizationResult>                           \
                {                                                                                             \
                  if (c == NumTraits::ConstantType(0)) {                                                      \
                    return none<NormalizationResult>();                                                       \
                  } else {                                                                                    \
                    auto rhs = Sum<NumTraits>::numeral(NumTraits::oneC / c);                                  \
                    return some<NormalizationResult>(Sum<NumTraits>::mul(results[0], rhs));                   \
                  }                                                                                           \
                });                                                                                           \
        } 

        NUM_CASE( IntTraits)
        NUM_CASE( RatTraits)
        NUM_CASE(RealTraits)
        FRAC_CASE( RatTraits)
        FRAC_CASE(RealTraits)
#     undef NUM_CASE
#     undef FRAC_CASE
        default:
          {}
      }
      return Optional<NormalizationResult>();
    } 

    NormalizationResult operator()(TypedTermList t, NormalizationResult* ts) const
    { 
      if (t.isVar()) {
        auto var = PolyNf(Variable(t.var()));
        switch (t.sort()) {
#         define VAR_CASE(NumTraits)                                                                          \
            case NumTraits::sort: return NormalizationResult(Sum<NumTraits>(Prod<NumTraits>(var)));
          VAR_CASE( IntTraits)
          VAR_CASE( RatTraits)
          VAR_CASE(RealTraits)
#         undef VAR_CASE
          default:
            return NormalizationResult(var);
        }
      } else {
        ASS(t.isTerm());
        auto term = t.term();
        auto fn = FuncId(term->functor());
        if (fn.isInterpreted()) {
          auto maybePoly = normalizeInterpreted(fn.interpretation(), ts);
          if (maybePoly.isSome()) {
            return std::move(maybePoly).unwrap();
          }
        } 
        auto out = unique(FuncTerm(
                fn, 
                Stack<PolyNf>::fromIterator(
                    iterTraits(getArrayishObjectIterator<mut_ref_t>(ts, fn.arity()))
                    .map( [](NormalizationResult& r) -> PolyNf { return toPolyNf(r); }))
              )
            );

#     define NUMERAL_CASE(Num)                                                                                \
          if (fn.template tryNumeral<Num ## Traits>().isSome())                                               \
            return NormalizationResult(Sum<Num ## Traits>::numeral(out));
          
        NUMERAL_CASE(Int )
        NUMERAL_CASE(Rat )
        NUMERAL_CASE(Real)

#     undef NUMERAL_CASE

        return NormalizationResult(PolyNf(out));
      }
    }
  };
  NormalizationResult r = evaluateBottomUp(t, Eval{}, memo);
  return toPolyNf(r);
}


} // Kernel.hpp
#undef DEBUG

#endif // __POLYNOMIAL_NORMALIZER_HPP__
