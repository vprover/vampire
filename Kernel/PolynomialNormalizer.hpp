
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

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
#include "Kernel/Polynomial.hpp"
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/UniqueShared.hpp"


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__
#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Kernel {

//   explicit TermEvalResult(TermList t) : Coproduct(t) {}
//   TermEvalResult(Coproduct     && super) : Coproduct(std::move(super)) {}
//   TermEvalResult(Coproduct      & super) : Coproduct(          super ) {}
//   TermEvalResult(Coproduct const& super) : Coproduct(          super ) {}
//   bool isPoly() const& { return is<1>(); }
//   AnyPoly const& asPoly() const& { return unwrap<1>(); }
//   AnyPoly      & asPoly()      & { return unwrap<1>(); }
//   template<class Config>
//   TermList toTerm() { return match<TermList> ( 
//       [](TermList& t) { return t; },
//       [](AnyPoly& p) { return p.template toTerm_<Config>(); }
//       );
//   }
// };

namespace Memo {

  template<class EvalFn>
  struct None 
  {
    using Result = typename std::result_of<EvalFn(Variable)>::type;
    template<class Init> Result getOrInit(Term* _orig, Init init) { return init(); }
    Result* getPtr(Term* _orig) { return nullptr; }
  };

  template<class EvalFn>
  class Hashed 
  {
    using Result = typename std::result_of<EvalFn(Variable)>::type;

    Map<Term*, Result> _memo;

  public:
    Hashed() : _memo(decltype(_memo)()) {}
    template<class Init> Result getOrInit(Term* orig, Init init) { return _memo.getOrInit(std::move(orig), init); }
    Result* getPtr(Term* orig) { return _memo.getPtr(orig); }
  };

}


template<class T>
T assertionViolation() {ASSERTION_VIOLATION}

/** TODO document */
template<class EvalFn, class Memo = Memo::None<EvalFn>>
typename std::result_of<EvalFn(Variable)>::type evaluateBottomUp(TermList term_, EvalFn evaluateStep, Memo& memo) 
{
  using Result = typename std::result_of<EvalFn(Variable)>::type;

  static_assert(std::is_same<typename std::result_of<EvalFn(Term*, Result*)>::type
                            ,Result                                               >::value
                            ,"EvalFn must be of signature `Result evaluateStep(Term*, Result*)`");
  CALL("PolynomialNormalizer::evaluate(TermList)")
  if (term_.isVar()) {
    return evaluateStep(Variable(term_.var())); //TODO memo variables as well.
  }
  Term* term = term_.term();
  
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

  static Stack<TermList*> recursion(8);
  static Stack<Term*> terms(8);
  static vector<ResultWrapper> args;

  recursion.push(term->args());
  terms.push(term);

  TermList* cur;
  while (!recursion.isEmpty()) {

    cur = recursion.pop();

    if (!cur->isEmpty()) {

      recursion.push(cur->next());

      if(cur->isVar()) {
        // variables are not evaluated
        args.emplace_back(evaluateStep(Variable(cur->var())));

      } else {
        ASS(cur->isTerm());

        Term* t = cur->term();

        auto cached = memo.getPtr(t);
        if (cached == nullptr) {
           terms.push(t);
           recursion.push(t->args());
        } else {
          args.emplace_back(*cached); 
        }
      }


    } else /* cur->isEmpty() */ { 

      ASS(!terms.isEmpty()) 

      Term* orig = terms.pop();

      Result eval = memo.getOrInit(std::move(orig), 
          [&](){ 
            Result* argLst = NULL;
            if (orig->arity() != 0) {
              ASS(args.size() >= orig->arity());
              argLst=static_cast<Result*>(&args[args.size() - orig->arity()]);
            }

            return evaluateStep(orig,argLst);
            // ::new(toInit) Result(std::move(eval));
          });

      DEBUG("evaluated: ", orig->toString(), " -> ", eval);

      args.resize(args.size() - orig->arity());
      args.emplace_back(std::move(eval));
    }

  }
  ASS_REP(recursion.isEmpty(), recursion)
    

  ASS(args.size() == 1);
  Result out = std::move(args[0]);
  args.clear();
  return std::move(out);
}

inline PolyNf PolyNf::normalize(TermList t) 
{
  // using Result = Coproduct<PolyNf, Vec<>;

  struct Eval 
  {
    PolyNf operator()(Variable v) { return v; }
    PolyNf operator()(Term* orig, PolyNf* evaluatedArgs) 
    {
      FuncId func(orig->functor());
      Stack<PolyNf> s(func.arity());
      s.loadFromIterator(getArrayishObjectIterator(evaluatedArgs, func.arity()));
      return unique(FuncTerm(
            func, 
            std::move(s)
          ));
    }
  };
  Memo::None<Eval> memo;
  return evaluateBottomUp(t, Eval{}, memo);
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
    PolyNf operator()(Variable v) 
    { return v; }

    PolyNf operator()(Term* t, PolyNf* ts) 
    { return norm.evaluateStep(t, ts); }
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
