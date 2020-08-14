
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


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {

namespace Memo {

  template<class EvalFn>
  struct None 
  {
    using Result = typename EvalFn::Result;
    using Arg    = typename EvalFn::Arg;
    Result* getPtr(Arg _orig) { return nullptr; }
    template<class Init> Result getOrInit(Arg orig, Init init) { return init(); }
  };

  template<class EvalFn>
  class Hashed 
  {
    using Result = typename EvalFn::Result;
    using Arg    = typename EvalFn::Arg;

    Map<Arg, Result> _memo;

  public:
    Hashed() : _memo(decltype(_memo)()) {}

    template<class Init> Result getOrInit(Arg orig, Init init) 
    { return _memo.getOrInit(std::move(orig), init); }

    Result* getPtr(const Arg& orig) 
    { return _memo.getPtr(orig); }
  };

} // namespace Memo
} // namespace Kernel
#include "Kernel/Polynomial.hpp"


namespace Kernel {

template<class T>
T assertionViolation() {ASSERTION_VIOLATION}

template<class A> 
struct ChildIter
{
  A next();
  bool hasNext();
  A self();
  unsigned nChildren();
};

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

  ChildIter(PolyNf self) : _self(self.template match<Inner>(
        [&](UniqueShared<FuncTerm> self) { return Inner(FuncTermChildIter( self ));            },
        [&](Variable               self) { return Inner(VariableChildIter( self ));            },
        [&](AnyPoly                self) { return Inner(PolynomialChildIter(std::move(self))); }
      ))
  {}

  PolyNf next() 
  { ASS(hasNext()); return _self.template collapsePoly<PolyNf>(Polymorphic::next{}); }

  bool hasNext() const 
  { return _self.template collapsePoly<bool>(Polymorphic::hasNext{}); }

  unsigned nChildren() const 
  { return _self.template collapsePoly<unsigned>(Polymorphic::nChildren{}); }

  PolyNf self() const 
  { return _self.template collapsePoly<PolyNf>(Polymorphic::self{}); }
};

/** TODO document */
template<class EvalFn, class Memo = Memo::None<EvalFn>>
typename EvalFn::Result evaluateBottomUp(typename EvalFn::Arg term, EvalFn evaluateStep, Memo& memo) 
{
  CALL("evaluateBottomUp(...)")
  using Result = typename EvalFn::Result;
  using Arg    = typename EvalFn::Arg;

  
  /** only used in order to be able to create a fake default constructor for Result, that is required by
   * std::vector::resize. The constructor will actually never be called.
   */
  struct ResultWrapper : Result
  {
    ResultWrapper(Result     && res) : Result(std::move(res)) {  }
    ResultWrapper(Result      & res) : Result(          res ) {  }
    ResultWrapper(Result const& res) : Result(          res ) {  }
    ResultWrapper() : Result(assertionViolation<Result>()) {  }
  };

  /* recursion state. Contains a stack of items that are being recursed on. */
  Stack<ChildIter<Arg>> recState;
  vector<ResultWrapper> recResults;

  recState.push(ChildIter<Arg>(term));

  while (!recState.isEmpty()) {

    if (recState.top().hasNext()) {
      Arg t = recState.top().next();

      auto cached = memo.getPtr(t);
      if (cached == nullptr) {
         recState.push(ChildIter<Arg>(t));
      } else {
        recResults.emplace_back(*cached); 
      }

    } else { 

      ChildIter<Arg> orig = recState.pop();

      Result eval = memo.getOrInit(std::move(orig.self()),
          [&](){ 
            Result* argLst = NULL;
            if (orig.nChildren() != 0) {
              ASS_GE(recResults.size(), orig.nChildren());
              argLst = static_cast<Result*>(&recResults[recResults.size() - orig.nChildren()]);
            }
            return evaluateStep(orig.self(), argLst);
          });

      DEBUG("evaluated: ", orig.self(), " -> ", eval);

      recResults.resize(recResults.size() - orig.nChildren());
      recResults.emplace_back(std::move(eval));
    }

  }
  ASS(recState.isEmpty())
    

  ASS(recResults.size() == 1);
  Result out = std::move(recResults[0]);
  recResults.clear();
  return std::move(out);
}

inline PolyNf PolyNf::normalize(TermList t) 
{



 
  // using Result = Coproduct<PolyNf, Vec<>;

  // struct Eval 
  // {
  //   PolyNf operator()(Variable v) { return v; }
  //   PolyNf operator()(Term* orig, PolyNf* evaluatedArgs) 
  //   {
  //     FuncId func(orig->functor());
  //     Stack<PolyNf> s(func.arity());
  //     s.loadFromIterator(getArrayishObjectIterator(evaluatedArgs, func.arity()));
  //     return unique(FuncTerm(
  //           func, 
  //           std::move(s)
  //         ));
  //   }
  // };
  // Memo::None<Eval> memo;
  // return evaluateBottomUp(t, Eval{}, memo);
  // TODO implement
  ASSERTION_VIOLATION
}


class LitEvalResult : public Lib::Coproduct<Literal*, bool> 
{
private:
  explicit LitEvalResult(Coproduct&& l) : Coproduct(std::move(l)) {}
public:
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

//
// /**
//  * For every Theory::Interpretation that represents a predicate one specialization of this template function must be provided.
//  */
// template<Theory::Interpretation inter> 
// LitEvalResult evaluateLit(Literal* orig, PolyNf* evaluatedArgs);

/**
 * For every Theory::Interpretation that represents a function one specialization of this struct must be provided.
 *
 * The parameter @b PolynomialNormalizerConfig is expected to be one of the tryInterpretConstant in @b PolynomialNormalizerConfig
 */
template<Theory::Interpretation inter>
struct FunctionEvaluator {
  template<class PolynomialNormalizerConfig>
  static PolyNf evaluate(Term* orig, PolyNf* evaluatedArgs);
};


template<Theory::Interpretation inter>
struct PredicateEvaluator {
  template<class PolynomialNormalizerConfig>
  static LitEvalResult evaluate(Literal* orig, PolyNf* evaluatedArgs);
};

#include "Kernel/PolynomialNormalizer/FunctionEvaluator.hpp"
#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Implementation of literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config>
inline Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  auto arity = orig->arity();

  Stack<TermList> args(arity);
  for (int i = 0; i < arity; i++) {
    args.push(evaluatedArgs[i].template toTerm<Config>());
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
#define HANDLE_NUM_CASES(NUM) \
      IGNORE_CASE(NUM ## _IS_INT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_RAT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_REAL) /* TODO */ \
      HANDLE_CASE(NUM ## _GREATER) \
      HANDLE_CASE(NUM ## _GREATER_EQUAL) \
      HANDLE_CASE(NUM ## _LESS) \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  //TODO create function theory->tryInterpret(Predicate|Function)
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
{ return AnyPoly(Polynom<number>(c)); }


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main term  evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


template<class Config> PolyNf PolynomialNormalizer<Config>::evaluate(TermList term) const {
  struct Eval 
  {
    const PolynomialNormalizer& norm;

    using Result = PolyNf;
    using Arg    = TermList;

    PolyNf operator()(TermList t, PolyNf* ts) 
    { 
      if (t.isVar()) {
        return PolyNf(Variable(t.var()));
      } else {
        return norm.evaluateStep(t.term(), ts); 
      }
    }
  };
  static Memo::Hashed<Eval> memo;
  return evaluateBottomUp(term, Eval{ *this }, memo);
}

template<class Config> PolyNf PolynomialNormalizer<Config>::evaluate(Term* term) const 
{ return evaluate(TermList(term)); }


template<class Config>
inline PolyNf createTerm(unsigned fun, PolyNf* evaluatedArgs) 
{ return unique(FuncTerm(FuncId(fun), evaluatedArgs)); }


template<class Config> PolyNf PolynomialNormalizer<Config>::evaluateStep(Term* orig, PolyNf* args) const {
  CALL("PolynomialNormalizer::evaluateStep(Term* orig, PolyNf* args)")
  DEBUG("evaluating ", *orig)

#define HANDLE_CASE(INTER) case Interpretation::INTER: return FunctionEvaluator<Interpretation::INTER>::evaluate<Config>(orig, args); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return createTerm<Config>(functor, args);


#define HANDLE_CONSTANT_CASE(Num) \
  { \
    Num ## ConstantType c; \
    if (theory->tryInterpretConstant(orig, c)) { \
      return evaluateConst<NumTraits<Num ## ConstantType>>(c); \
    } \
  } \

#define HANDLE_NUM_CASES(NUM) \
    HANDLE_CASE(NUM ## _UNARY_MINUS) \
    HANDLE_CASE(NUM ## _PLUS) \
    HANDLE_CASE(NUM ## _MINUS) \
    HANDLE_CASE(NUM ## _MULTIPLY) \
    HANDLE_CASE(NUM ## _QUOTIENT_E) \
    HANDLE_CASE(NUM ## _QUOTIENT_T) \
    HANDLE_CASE(NUM ## _QUOTIENT_F) \
    HANDLE_CASE(NUM ## _REMAINDER_E) \
    HANDLE_CASE(NUM ## _REMAINDER_T) \
    HANDLE_CASE(NUM ## _REMAINDER_F) \
    HANDLE_CASE(NUM ## _FLOOR) \
    HANDLE_CASE(NUM ## _CEILING) \
    HANDLE_CASE(NUM ## _TRUNCATE) \
    HANDLE_CASE(NUM ## _TO_INT) \
    HANDLE_CASE(NUM ## _TO_RAT) \
    HANDLE_CASE(NUM ## _TO_REAL) \

  auto functor = orig->functor();
  auto sym = env.signature->getFunction(functor);

  try {
    if (sym->interpreted()) {
      if (sym->interpretedNumber()) {
          HANDLE_CONSTANT_CASE(Integer)
          HANDLE_CONSTANT_CASE(Rational)
          HANDLE_CONSTANT_CASE(Real)
          ASS_REP(false, "unexpected interpreted number: " + orig->toString())
      } else {
        auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
        switch (inter) {

          /* common number functions*/
          HANDLE_NUM_CASES(INT)
          HANDLE_NUM_CASES(RAT)
          HANDLE_NUM_CASES(REAL)

          /* integer functions */
          HANDLE_CASE(INT_SUCCESSOR)
          HANDLE_CASE(INT_ABS)

          /* rational functions */
          HANDLE_CASE(RAT_QUOTIENT)
          IGNORE_CASE(RAT_ROUND)  //TODO

          /* real functions */
          HANDLE_CASE(REAL_QUOTIENT)
          IGNORE_CASE(REAL_ROUND)  //TODO

          /* ignored */
          IGNORE_CASE(ARRAY_SELECT)
          IGNORE_CASE(ARRAY_BOOL_SELECT)
          IGNORE_CASE(ARRAY_STORE)

          default:
            ASS_REP(false, "unexpected interpreted function: " + orig->toString())
        }
      }

    }
  } catch (MachineArithmeticException) { /* nop */ }
  // /* uninterpreted or evaluation failed */
  return createTerm<Config>(functor, args);
}



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
