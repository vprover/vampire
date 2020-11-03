
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

class PolyNf::Iter {
  Stack<BottomUpChildIter<PolyNf>> _stack;
public:
  Iter(Iter&&) = default;
  Iter& operator=(Iter&&) = default;
  Iter(PolyNf p) : _stack(decltype(_stack){ BottomUpChildIter<PolyNf>(p) }) {  }
  DECL_ELEMENT_TYPE(PolyNf);

  PolyNf next() {
    CALL("PolyNf::Iter::next")
    ASS(_stack.size() != 0)
    while(_stack.top().hasNext()) {
      ASS(_stack.size() != 0)
      _stack.push(BottomUpChildIter<PolyNf>(_stack.top().next()));
    }
    ASS(_stack.size() != 0)
    return _stack.pop().self();
  }

  bool hasNext() const 
  { 
    CALL("PolyNf::Iter::hasNext")
    return !_stack.isEmpty(); 
  }
};


inline IterTraits<PolyNf::Iter> PolyNf::iter() const 
{ return iterTraits(Iter(*this)); }


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
    std::sort(sbegin, send); // TODO different sorting(s)
    // std::sort(summands.begin(), summands.end()); // TODO different sorting(s)

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

inline PolyNf PolyNf::normalize(TypedTermList t) 
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

class PolynomialNormalizer {
public:
  Optional<LitSimplResult> evaluate(Literal* in) const;
  Optional<PolyNf> evaluate(TermList in, unsigned sortNumber) const;
  Optional<PolyNf> evaluate(Term* in) const;
  Optional<PolyNf> evaluate(PolyNf in) const;
  Optional<PolyNf> evaluate(TypedTermList in) const;

private:
  struct RecursionState;
  Optional<LitSimplResult> evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const;

  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;
};

template<Theory::Interpretation inter>
struct PredicateEvaluator {
  template<class PolynomialNormalizerConfig>
  static LitSimplResult evaluate(Literal* orig, PolyNf* evaluatedArgs);
};

template<class Number>
UniqueShared<Polynom<Number>> intoPoly(PolyNf p) 
{ 
  CALL("intoPoly(PolyNf p)")
  return unique(
    p.is<AnyPoly>() ? *p.unwrap<AnyPoly>()
                        .unwrap<UniqueShared<Polynom<Number>>>()
                    : Polynom<Number>(p)
      );
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Implementation of literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

inline Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  if (orig->isEquality()) {
    return Literal::createEquality(
          orig->polarity(), 
          evaluatedArgs[0].toTerm(), 
          evaluatedArgs[1].toTerm(), 
          SortHelper::getArgSort(orig, 0));
  } else {
    auto arity = orig->arity();
    Stack<TermList> args(arity);
    for (int i = 0; i < arity; i++) {
      args.push(evaluatedArgs[i].toTerm());
    }
    return Literal::create(orig, args.begin());
  }
}


inline Optional<LitSimplResult> PolynomialNormalizer::evaluate(Literal* lit) const {
  Stack<PolyNf> terms(lit->arity());
  auto anyChange = false;
  for (int i = 0; i < lit->arity(); i++) {
    auto term = *lit->nthArgument(i);
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getArgSort(lit, i)));
    auto ev = evaluate(norm);
    anyChange = anyChange || ev.isSome();
    terms.push(std::move(ev).unwrapOrElse([&](){ return norm; }));
  }
  auto ev = evaluateStep(lit, terms.begin());
  anyChange = anyChange || ev.isSome();

  if (anyChange) {
    return Optional<LitSimplResult>(std::move(ev)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); }));
  } else {
    return Optional<LitSimplResult>();
  }
}

inline Optional<LitSimplResult> PolynomialNormalizer::evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialNormalizer::evaluateStep(Literal* term)")
  DEBUG("evaluating: ", orig->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return Optional<LitSimplResult>();
#define HANDLE_NUM_CASES(NUM)                                                                                 \
      IGNORE_CASE(NUM ## _IS_INT) /* TODO */                                                                  \
      IGNORE_CASE(NUM ## _IS_RAT) /* TODO */                                                                  \
      IGNORE_CASE(NUM ## _IS_REAL) /* TODO */                                                                 \
      HANDLE_CASE(NUM ## _GREATER)                                                                            \
      HANDLE_CASE(NUM ## _GREATER_EQUAL)                                                                      \
      HANDLE_CASE(NUM ## _LESS)                                                                               \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  auto sym = env.signature->getPredicate(orig->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)

      default:
        // WARN("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return Optional<LitSimplResult>();
    }
  } else {
    return Optional<LitSimplResult>();
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Number Constants 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
PolyNf evaluateConst(typename number::ConstantType c) 
{ return PolyNf(AnyPoly(unique(Polynom<number>(c)))); }


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main term  evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


template<class Number>
Optional<PolyNf> trySimplifyUnaryMinus(PolyNf* evalArgs)
{
  CALL("trySimplifyUnaryMinus(PolyNf*)")
  // using Const = typename Number::ConstantType;
  return some<PolyNf>(PolyNf(AnyPoly(unique(
          intoPoly<Number>(evalArgs[0])
              ->flipSign()
            ))));
}

template<class Number, class Clsr>
inline Optional<PolyNf> trySimplifyConst2(PolyNf* evalArgs, Clsr f) 
{
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (lhs.isSome() && rhs.isSome()) {
    return some<PolyNf>(PolyNf(AnyPoly(unique(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

inline Optional<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
{
  CALL("trySimplify(Theory::Interpretation i, PolyNf* evalArgs) ")
  try {
    switch (i) {

#define CONSTANT_CASE(Num, func, expr)                                                                        \
      case Num##Traits:: func ## I:                                                                           \
        {                                                                                                     \
          using Const = typename Num##Traits::ConstantType;                                                   \
          return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
        }                                                                                                     \

#define QUOTIENT_REMAINDER_CASES(Num, X)                                                                      \
      CONSTANT_CASE(Num,  quotient##X, l. quotient##X(r))                                                     \
      CONSTANT_CASE(Num, remainder##X, l.remainder##X(r))                                                     \

#define FRAC_CASE(Num)                                                                                        \
      CONSTANT_CASE(Num, div, l / r)

#define NUM_CASE(Num)                                                                                         \
      case Num ## Traits::minusI:     return trySimplifyUnaryMinus<Num ## Traits>(evalArgs);                  \

      NUM_CASE(Int)
      NUM_CASE(Rat)
      NUM_CASE(Real)
      QUOTIENT_REMAINDER_CASES(Int, E)
      QUOTIENT_REMAINDER_CASES(Int, T)
      QUOTIENT_REMAINDER_CASES(Int, F)

      FRAC_CASE(Rat)
      FRAC_CASE(Real)

  // TODO evaluate conversion functions
  // TODO evaluate INT_ABS
  // TODO evaluate INT_SUCCESSOR
  // TODO evaluate FRAC_QUOTIENT
  // TODO evaluate FRAC_ROUND
  // TODO evaluate NUM_TO_NUM
  // TODO evaluate NUM_TRUNCATE

#undef NUM_CASE
#undef QUOTIENT_REMAINDER_CASES
#undef CONSTANT_CASE

      default:
        return none<PolyNf>();
    }
  } catch (MachineArithmeticException) {
    return none<PolyNf>();

  } catch (DivByZeroException) {
    return none<PolyNf>();
  }
}

inline Optional<PolyNf> PolynomialNormalizer::evaluate(TermList term, unsigned sortNumber) const 
{ return evaluate(TypedTermList(term, sortNumber)); }

inline Optional<PolyNf> PolynomialNormalizer::evaluate(Term* term) const 
{ return evaluate(TypedTermList(term)); }

inline Optional<PolyNf> PolynomialNormalizer::evaluate(TypedTermList term) const 
{ return evaluate(PolyNf::normalize(term)); }

inline Optional<PolyNf> PolynomialNormalizer::evaluate(PolyNf normalized) const 
{
  CALL("PolynomialNormalizer::evaluate(TypedTermList term) const")

  // auto norm = PolyNf::normalize(term);
  DEBUG("evaluating ", normalized)
  struct Eval 
  {
    const PolynomialNormalizer& norm;

    using Result = PolyNf;
    using Arg    = PolyNf;

    PolyNf operator()(PolyNf orig, PolyNf* ts) 
    { 
      return orig.match(
          [&](UniqueShared<FuncTerm> f)  -> PolyNf
          { 
            return f->function().tryInterpret()
              .andThen( [&](Theory::Interpretation && i)  -> Optional<PolyNf>
                { return trySimplify(i, ts); })
              .unwrapOrElse([&]() -> PolyNf
                { return PolyNf(unique(FuncTerm(f->function(), ts))); });

          }, 

          [&](Variable v) 
          { return v; },

          [&](AnyPoly p) 
          { return p.simplify(ts); }
      );
    }
  };
  static Memo::Hashed<PolyNf, PolyNf> memo;
  auto out = evaluateBottomUp(normalized, Eval{ *this }, memo);
  if (out == normalized) {
    return Optional<PolyNf>();
  } else {
    return Optional<PolyNf>(out);
  }
}

template<class Config>
inline PolyNf createTerm(unsigned fun, PolyNf* evaluatedArgs) 
{ return unique(FuncTerm(FuncId(fun), evaluatedArgs)); }


} // Kernel.hpp
#undef DEBUG


template<class T> struct std::hash<Lib::Stack<T>> 
{
  size_t operator()(Lib::Stack<T> const& s) const 
  { return StackHash<StlHash<T>>::hash(s); }
};

template<> struct std::hash<Kernel::FuncId> 
{
  size_t operator()(Kernel::FuncId const& f) const 
  { return std::hash<unsigned>{}(f._num); }
};

template<> struct std::hash<Kernel::FuncTerm> 
{
  size_t operator()(Kernel::FuncTerm const& f) const 
  { return Lib::HashUtils::combine(std::hash<Kernel::FuncId>{}(f._fun), std::hash<Stack<Kernel::PolyNf>>{}(f._args));  }
};


template<> struct std::hash<Kernel::PolyNf> 
{
  size_t operator()(Kernel::PolyNf const& f) const 
  { return std::hash<Kernel::PolyNfSuper>{}(f); }
};

template<> struct std::hash<Kernel::Variable>
{
  size_t operator()(Kernel::Variable const& self)
  { return std::hash<unsigned>{}(self._num); }
};

#endif // __POLYNOMIAL_NORMALIZER_HPP__
