
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


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__

#define DEBUG(...)  DBG(__VA_ARGS__)

namespace Kernel {

namespace Memo {

  /** a mocked memoization that does not store any results */
  template<class Arg, class Result>
  struct None 
  {
    Optional<Result> get(Arg) 
    { return Optional<Result>(); }

    template<class Init> Result getOrInit(Arg const& orig, Init init) 
    { return init(); }
  };

  /** a memoization realized as a hashmap */
  template<class Arg, class Result>
  class Hashed 
  {
    Map<Arg, Result> _memo;

  public:
    Hashed() : _memo(decltype(_memo)()) {}

    template<class Init> Result getOrInit(Arg const& orig, Init init) 
    { return _memo.getOrInit(Arg(orig), init); }

    Optional<Result> get(const Arg& orig) 
    { 
      auto out = _memo.getPtr(orig);
      if (out) {
        return Optional<Result>(*out);
      } else {
        return Optional<Result>();
      }
    }
  };

} // namespace Memo

//TODO document
template<class A> 
struct ChildIter
{
  A next();
  bool hasNext();
  A self();
  unsigned nChildren();
};


/** 
 * Evaluates a term-like datastructure (i.e.: a directed acyclic graph), without using recursion.
 *
 * Optionally a memoization method (i.e. a class from Kernel::Memo) can be specified. The memo can be a static,
 * variable, in order to keep cached results for multiple runs of the funcion. 
 *
 * The term-ish structure is evaluated according to the structure EvalFn. It is expected to have the following structure:
 * class EvalFn {
 *    using Arg    = ...; // <- the term-ish structure
 *    using Result = ...; // <- the type the structure will be evaluated to
 *
 *    // The actual evaluation funciton. It will be called once for each node in the directed acyclic graph, together with 
 *    // the already recursively evaluated children.
 *    Result operator()(Arg const& orig, Result* evaluatedChildren); 
 * }
 * 
 * The term to be evaluated will be traversed using a ChildIter<Arg>. 
 */
template<class EvalFn, class Memo = Memo::None<typename EvalFn::Arg, typename EvalFn::Result>>
typename EvalFn::Result evaluateBottomUp(typename EvalFn::Arg const& term, EvalFn evaluateStep, Memo& memo) 
{
  CALL("evaluateBottomUp(...)")
  using Result = typename EvalFn::Result;
  using Arg    = typename EvalFn::Arg;

  
  /* recursion state. Contains a stack of items that are being recursed on. */
  Stack<ChildIter<Arg>> recState;
  Stack<Result> recResults;

  recState.push(ChildIter<Arg>(term));

  while (!recState.isEmpty()) {

    if (recState.top().hasNext()) {
      Arg t = recState.top().next();

      Optional<Result> cached = memo.get(t);
      if (cached.isSome()) {
        recResults.pushMv(std::move(cached).unwrap()); 
      } else {
        recState.push(ChildIter<Arg>(t));
      }

    } else { 

      ChildIter<Arg> orig = recState.pop();

      Result eval = memo.getOrInit(orig.self(), [&](){ 
            Result* argLst = NULL;
            if (orig.nChildren() != 0) {
              ASS_GE(recResults.size(), orig.nChildren());
              argLst = static_cast<Result*>(&recResults[recResults.size() - orig.nChildren()]);
            }
            return evaluateStep(orig.self(), argLst);
          });

      DEBUG("evaluated: ", orig.self(), " -> ", eval);

      recResults.pop(orig.nChildren());
      recResults.pushMv(std::move(eval));
    }
  }
  ASS(recState.isEmpty())
    

  ASS(recResults.size() == 1);
  return std::move(recResults.pop());
}

} // namespace Kernel
#include "Kernel/Polynomial.hpp"


namespace Kernel {

template<>
struct ChildIter<TermList>
{
  TermList _self;
  unsigned _idx;

  ChildIter(TermList self) : _self(self), _idx(0)
  {}

  TermList next() 
  {
    ASS(hasNext());
    return *_self.term()->nthArgument(_idx++);
  }
  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->arity(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->arity(); }

  TermList self() const 
  { return _self; }
};


POLYMORPHIC_FUNCTION(bool    , hasNext  , const& t,) { return t.hasNext();   }
POLYMORPHIC_FUNCTION(PolyNf  , next     ,      & t,) { return t.next();      }
POLYMORPHIC_FUNCTION(unsigned, nChildren, const& t,) { return t.nChildren(); }
POLYMORPHIC_FUNCTION(PolyNf  , self     , const& t,) { return PolyNf(t._self);       }

template<>
struct ChildIter<PolyNf>
{
  struct PolynomialChildIter 
  {
    AnyPoly _self;
    unsigned _idx1;
    unsigned _idx2;
    unsigned _nChildren;

    PolynomialChildIter(AnyPoly self) : _self(self), _idx1(0), _idx2(0), _nChildren(0)
    {
      while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
        _idx1++;
      }
      for (unsigned i = 0; i < _self.nSummands(); i++) {
        _nChildren += self.nFactors(i);
      }
    }

    bool hasNext() const
    { return _idx1 < _self.nSummands(); }

    PolyNf next() 
    { 
      auto out = _self.termAt(_idx1, _idx2++);
      if (_idx2 >= _self.nFactors(_idx1)) {
        _idx1++;
        while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
          _idx1++;
        }
        _idx2 = 0;
      }
      return out;
    }

    unsigned nChildren() const
    { return _nChildren; }
  };

  struct FuncTermChildIter 
  {

    UniqueShared<FuncTerm> _self;
    unsigned _idx;

    FuncTermChildIter(UniqueShared<FuncTerm> self) : _self(self), _idx(0) {}

    bool hasNext() const
    { return _idx < _self->arity(); }

    PolyNf next() 
    { return _self->arg(_idx++); }

    unsigned nChildren() const
    { return _self->arity(); }
  };


  struct VariableChildIter 
  {
    Variable _self;
    VariableChildIter(Variable self) : _self(self) {}

    bool hasNext() const
    { return false; }

    PolyNf next() 
    { ASSERTION_VIOLATION }

    unsigned nChildren() const
    { return 0; }
  };

  using Inner = Coproduct<FuncTermChildIter, VariableChildIter, PolynomialChildIter>;
  Inner _self;

  ChildIter(PolyNf self) : _self(self.match(
        [&](UniqueShared<FuncTerm> self) { return Inner(FuncTermChildIter( self ));            },
        [&](Variable               self) { return Inner(VariableChildIter( self ));            },
        [&](AnyPoly                self) { return Inner(PolynomialChildIter(std::move(self))); }
      ))
  {}

  PolyNf next() 
  { ASS(hasNext()); return _self.apply(Polymorphic::next{}); }

  bool hasNext() const 
  { return _self.apply(Polymorphic::hasNext{}); }

  unsigned nChildren() const 
  { return _self.apply(Polymorphic::nChildren{}); }

  PolyNf self() const 
  { return _self.apply(Polymorphic::self{}); }
};

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
  { return out << "Sum" << self._factors; }
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
  using Prod = Kernel::Prod<Number>;
  Stack<Prod> _summands; 

  explicit Sum(Prod&& m0, Prod&& m1) : _summands(Stack<Prod>(2)) 
  {
    _summands.pushMv(std::move(m0));
    _summands.pushMv(std::move(m1));
  }

public:

  explicit Sum(Prod&& m0) : _summands(Stack<Prod>(1)) 
  { _summands.pushMv(std::move(m0)); }

  Sum(Sum&&) = default;
  Sum& operator=(Sum&&) = default;

  static NormalizationResult mul(PolyNf& t, Sum& p)
  {
    if (p._summands.size() == 1) {
      //  Poly(Mon(p0 * p1 * ... )) * t ==> Poly(Mon(t * p0 * ... ))
      p._summands[0]._factors.pushMv(std::move(t));
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
      lhs._summands[0]._factors.moveFromIterator(rhs._summands[0]._factors.iterator());
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

  static NormalizationResult add(NormalizationResult& lhs, NormalizationResult& rhs)
  {
    if (lhs.is<PolyNf>() && rhs.is<PolyNf>()) {
      return NormalizationResult(Sum(Prod(lhs.unwrap<PolyNf>()), Prod(rhs.unwrap<PolyNf>())));
    } else if (lhs.is<PolyNf>() || rhs.is<PolyNf>()) {
      Sum p = rhs.is<PolyNf>() ? std::move(lhs).unwrap<Sum>() : std::move(rhs).unwrap<Sum>();
      PolyNf  t = rhs.is<PolyNf>() ? rhs.unwrap< PolyNf>() : lhs.unwrap< PolyNf>();
      p._summands.pushMv(Prod(t));
      return NormalizationResult(std::move(p));
    } else {
      ASS(lhs.is<Sum>())
      ASS(rhs.is<Sum>())
      auto out = std::move(lhs).unwrap<Sum>();
      out._summands.moveFromIterator(rhs.unwrap<Sum>()._summands.iterator());
      return NormalizationResult(std::move(out));
    }
  }

  PolyNf polyNf()  const
  {
    using PolyPair  = Kernel::PolyPair<Number>;
    using Polynom   = Kernel::Polynom  <Number>;
    using MonomPair = Kernel::MonomPair<Number>;
    using Monom     = Kernel::Monom    <Number>;
    using Const     = typename Number::ConstantType;

    auto begin = _summands.begin();
    auto summands = Stack<PolyPair>::fromIterator(
        iterTraits(getArrayishObjectIterator<mut_ref_t>(begin, _summands.size()))
          .map([](Prod& p) {
            std::sort(p._factors.begin(), p._factors.end()); // TODO make different orderings possible
            Stack<MonomPair> monomFactors;
            auto iter = p._factors.begin();
            while (iter != p._factors.end()) {
              auto elem = *iter;
              unsigned cnt = 0;
              while (iter != p._factors.end() && *iter == elem) {
                cnt++;
                iter++;
              }
              ASS(cnt != 0);
              monomFactors.push(MonomPair(elem, cnt));
            }
            return PolyPair(Const(1), unique(Monom(std::move(monomFactors))));
          })
      );
    std::sort(summands.begin(), summands.end()); // TODO different sorting(s)

    // TODO insert into memo
    return PolyNf(AnyPoly(unique(Polynom(std::move(summands)))));
  }

  static NormalizationResult minus(NormalizationResult& inner)
  { 
    static NormalizationResult minusOne(PolyNf(unique(FuncTerm(FuncId(Number::constantT(-1)->functor()), nullptr))));
    return mul(inner, minusOne); 
  }

public:
  friend ostream& operator<<(ostream& out, Sum const& self) 
  { return out << "Prod" << self._summands; }
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
    DBGE(_cache.numberOfElements());
  }
};

inline PolyNf PolyNf::normalize(TermList t) 
{
  CALL("PolyNf::normalize")
  DEBUG("normalizing ", t)
  // static Memo::None<TermList, NormalizationResult> memo;
  NormalizationMemo memo;
  struct Eval 
  {
    using Arg    = TermList;
    using Result = NormalizationResult;

    Optional<NormalizationResult> normalizeInterpreted(Interpretation i, NormalizationResult* results) const
    {
      switch (i) {

#     define NUM_CASE(NUM, Num)                                                                                         \
        case Theory::Interpretation::NUM ## _MULTIPLY:                                                                  \
          return Sum<Num ## Traits>::mul(results[0], results[1]);                                                       \
        case Theory::Interpretation::NUM ## _PLUS:                                                                      \
          return Sum<Num ## Traits>::add(results[0], results[1]);                                                       \
        case Theory::Interpretation::NUM ## _UNARY_MINUS:                                                               \
          return Sum<Num ## Traits>::minus(results[0]);                                                                 \

        NUM_CASE(INT , Int )
        NUM_CASE(RAT , Rat )
        NUM_CASE(REAL, Real)

#     undef NUM_CASE
        default:
          {}
      }
      return Optional<NormalizationResult>();
    } 

    NormalizationResult operator()(TermList t, NormalizationResult* ts) const
    { 
      if (t.isVar()) {
        return NormalizationResult(PolyNf(Variable(t.var())));
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
                    .map( [](NormalizationResult& r) -> PolyNf { return toPolyNf(r); })
                )
              )
            );

#     define NUM_CASE(Num)                                                                                         \
          if (fn.template tryNumeral<Num ## Traits>().isSome())  \
            return NormalizationResult(Sum<Num ## Traits>(Prod<Num ## Traits>(out)));
          
        NUM_CASE(Int )
        NUM_CASE(Rat )
        NUM_CASE(Real)

#     undef NUM_CASE

        return NormalizationResult(PolyNf(out));
      }
    }
  };
  NormalizationResult r = evaluateBottomUp(t, Eval{}, memo);
  return toPolyNf(r);
}


class LitEvalResult : public Lib::Coproduct<Literal*, bool> 
{
private:
  explicit LitEvalResult(Coproduct&& l) : Coproduct(std::move(l)) {}
public:
  using super = Lib::Coproduct<Literal*, bool>;
  /**
   * returns whether the result is a trivial literal (top or bot)
   */
  inline bool isConstant() const& { return is<1>(); }
  inline bool unwrapConstant() const& { return unwrap<1>(); }
  inline Literal* unwrapLiteral() const& { return unwrap<0>(); }
  inline static LitEvalResult constant(bool b) { return LitEvalResult(Coproduct::template variant<1>(b)); }
  inline static LitEvalResult literal(Literal* b) { return LitEvalResult(Coproduct::template variant<0>(b)); }
};

namespace PolynomialNormalizerConfig {

  template<class Ord = std::less<TermList>>
  struct Simplification { 
    using Ordering = Ord;
    constexpr static bool usePolyMul = false;
  };

  template<class Ord = std::less<TermList>>
  struct Normalization { 
    using Ordering = Ord;
    constexpr static bool usePolyMul = true;
  };

}

template<class Config>
class PolynomialNormalizer {
public:
  LitEvalResult evaluate(Literal* in) const;
  PolyNf evaluate(TermList in) const;
  PolyNf evaluate(Term* in) const;

private:
  struct RecursionState;
  LitEvalResult evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const;

  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;
};

template<Theory::Interpretation inter>
struct PredicateEvaluator {
  template<class PolynomialNormalizerConfig>
  static LitEvalResult evaluate(Literal* orig, PolyNf* evaluatedArgs);
};

template<class Number>
UniqueShared<Polynom<Number>> intoPoly(PolyNf p) 
{ 
  CALL("intoPoly(PolyNf p)")
  return unique(
    p.is<AnyPoly>() ? p.unwrap<AnyPoly>()
                       .unwrap<UniqueShared<Polynom<Number>>>()
                    : Polynom<Number>(p)
      );
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Implementation of literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config>
inline Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  auto arity = orig->arity();

  Stack<TermList> args(arity);
  for (int i = 0; i < arity; i++) {
    args.push(evaluatedArgs[i].toTerm());
  }
  return Literal::create(orig, args.begin());
}


template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluate(Literal* lit) const {
  Stack<PolyNf> terms(lit->arity());
  for (int i = 0; i < lit->arity(); i++) {
    terms.push(evaluate(*lit->nthArgument(i)));
  }
  return evaluateStep(lit, terms.begin());
}

template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialNormalizer::evaluateStep(Literal* term)")
  DEBUG("evaluating: ", orig->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate<Config>(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return LitEvalResult::literal(createLiteral<Config>(orig, evaluatedArgs));
#define HANDLE_NUM_CASES(NUM)                                                                                           \
      IGNORE_CASE(NUM ## _IS_INT) /* TODO */                                                                            \
      IGNORE_CASE(NUM ## _IS_RAT) /* TODO */                                                                            \
      IGNORE_CASE(NUM ## _IS_REAL) /* TODO */                                                                           \
      HANDLE_CASE(NUM ## _GREATER)                                                                                      \
      HANDLE_CASE(NUM ## _GREATER_EQUAL)                                                                                \
      HANDLE_CASE(NUM ## _LESS)                                                                                         \
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
        // DBG("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return LitEvalResult::literal(createLiteral<Config>(orig, evaluatedArgs));
    }
  } else {
    return LitEvalResult::literal(createLiteral<Config>(orig, evaluatedArgs));
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
  return PolyNf(AnyPoly(unique(
          intoPoly<Number>(evalArgs[0])
              ->flipSign()
            )));
}

template<class Number, class Clsr>
inline Optional<PolyNf> trySimplifyConst2(PolyNf* evalArgs, Clsr f) 
{
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (lhs.isSome() && rhs.isSome()) {
    return PolyNf(AnyPoly(unique(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap())))));
  } else {
    return none<PolyNf>();
  }
}

inline Optional<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
{
  CALL("trySimplify(Theory::Interpretation i, PolyNf* evalArgs) ")
  switch (i) {

#define CONSTANT_CASE(Num, func)  \
    case Num##Traits:: func ## I:  \
      { \
        using Const = typename Num##Traits::ConstantType; \
        return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return l.func(r); }); \
      } \

#define QUOTIENT_REMAINDER_CASES(Num, X) \
    CONSTANT_CASE(Num, quotient##X) \
    CONSTANT_CASE(Num, remainder##X) \

#define NUM_CASE(Num) \
    case Num ## Traits::minusI:     return trySimplifyUnaryMinus<Num ## Traits>(evalArgs); \
    QUOTIENT_REMAINDER_CASES(Num, E) \
    QUOTIENT_REMAINDER_CASES(Num, T) \
    QUOTIENT_REMAINDER_CASES(Num, F) \

    NUM_CASE(Int)
    NUM_CASE(Rat)
    NUM_CASE(Real)

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
}

template<class Config> PolyNf PolynomialNormalizer<Config>::evaluate(TermList term) const 
{
  CALL("PolynomialNormalizer<Config>::evaluate(TermList term) const")

  auto norm = PolyNf::normalize(term);
  DEBUG("evaluating ", norm)
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
  return evaluateBottomUp(norm, Eval{ *this }, memo);
}

template<class Config> PolyNf PolynomialNormalizer<Config>::evaluate(Term* term) const 
{ return evaluate(TermList(term)); }


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
