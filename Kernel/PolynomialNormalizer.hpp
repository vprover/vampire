
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


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__
#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Kernel {


/**
 * A tagged union that is either a plain TermList, or a polynomial.
 */
class TermEvalResult : public Lib::Coproduct<TermList, AnyPoly> {
public:
  TermEvalResult() : Coproduct(Coproduct::template variant<0>(Kernel::TermList())) { }
  explicit TermEvalResult(TermList t) : Coproduct(t) {}
  TermEvalResult(Coproduct     && super) : Coproduct(std::move(super)) {}
  TermEvalResult(Coproduct      & super) : Coproduct(          super ) {}
  TermEvalResult(Coproduct const& super) : Coproduct(          super ) {}
  bool isPoly() const& { return is<1>(); }
  AnyPoly const& asPoly() const& { return unwrap<1>(); }
  AnyPoly      & asPoly()      & { return unwrap<1>(); }
  template<class Config>
  TermList toTerm() { return match<TermList> ( 
      [](TermList& t) { return t; },
      [](AnyPoly& p) { return p.template toTerm_<Config>(); }
      );
  }
};

class Variable 
{
  unsigned _num;
public: 
  explicit Variable(unsigned num) : _num(num) {}
  unsigned id() const { return _num; }
};


class FuncId 
{
  unsigned _num;
public: 
  explicit FuncId(unsigned num) : _num(num) {}
  unsigned arity() { return env.signature->getFunction(_num)->arity(); }
};


/** 
 * Smart pointer for aggressively shared objects.
 * TODO document, factor out.
 */
template<class T>
class Shared
{
  T* _elem;
  static Map<T, T*> _cached;

public:

  explicit Shared(T&& t);

  template<class U>
  friend bool operator==(Shared<U> const& l, Shared<U> const& r)
  { return l._elem == r._elem; }

  template<class U>
  friend bool operator!=(Shared<U> const& l, Shared<U> const& r)
  { return l._elem != r._elem; }

  operator T const&() const& { return *_elem; }
};


class PolyNf;

/**
 * Represents an ordenary complex term. In the PolyNF term tree.
 */
class FuncTerm 
{
  FuncId _fun;
  Stack<PolyNf> _args;
public:
  FuncTerm(FuncId f, Stack<PolyNf>&& args) : _fun(f), _args(std::move(args)) { }
};

/**
 * Represents the polynomial normal form of a term, that is used for performing several simplifications and evaluations.
 *
 * TODO add more documentation
 */
class PolyNf : Lib::Coproduct<Shared<FuncTerm>, Variable, AnyPoly>
{
  PolyNf(Shared<FuncTerm> t) : Coproduct(t) {}
  PolyNf(Variable t) : Coproduct(t) {}
  PolyNf(AnyPoly  t) : Coproduct(t) {}
public:
  PolyNf normalize(TermList t);
};

inline PolyNf PolyNf::normalize(TermList t) 
{
  if (t.isVar())  {
    return Variable(t.var());
  } else {
    // if (AnyPoly::isPoly(t.term())) {
    //   return AnyPoly::normalize(t.term());
    // } else {
    //   FuncId func(t.term()->functor())
    //   return FuncTerm(
    //         func, 
    //         t.term().args(),
    //         func.arity()
    //       )
    // }
  }
}

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

/** TODO document */
template<class EvalFn, class Memo = Memo::None<EvalFn>>
typename std::result_of<EvalFn(Variable)>::type evaluateBottomUp(Term* term, EvalFn evaluateStep, Memo& memo) 
{
  using Result = typename std::result_of<EvalFn(Variable)>::type;

  static_assert(std::is_same<typename std::result_of<EvalFn(Term*, Result*)>::type
                            ,Result                                               >::value
                            ,"EvalFn must be of signature `Result evaluateStep(Term*, Result*)`");
  CALL("PolynomialNormalizer::evaluate(Term* term)")

  static Stack<TermList*> recursion(8);
  // static Map<Term*, Result> memo;

  static Stack<Term*> terms(8);
  static vector<TermEvalResult> args;

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
            TermEvalResult* argLst = NULL;
            if (orig->arity() != 0) {
              ASS(args.size() >= orig->arity());
              argLst=&args[args.size() - orig->arity()];
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
  // TermEvalResult out = TermEvalResult::template variant<0>( TermList() );
  // std::move(std::make_move_iterator(args.begin()),
  //           std::make_move_iterator(args.end()),
  //           &out);
  Result out = std::move(args[0]);
  args.clear();
  return std::move(out);
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
  TermEvalResult evaluate(TermList in) const;
  TermEvalResult evaluate(Term* in) const;

private:
  struct RecursionState;
  LitEvalResult evaluateStep(Literal* orig, TermEvalResult* evaluatedArgs) const;

  TermEvalResult evaluateStep(Term* orig, TermEvalResult* evaluatedArgs) const;
};

//
// /**
//  * For every Theory::Interpretation that represents a predicate one specialization of this template function must be provided.
//  */
// template<Theory::Interpretation inter> 
// LitEvalResult evaluateLit(Literal* orig, TermEvalResult* evaluatedArgs);

/**
 * For every Theory::Interpretation that represents a function one specialization of this struct must be provided.
 *
 * The parameter @b PolynomialNormalizerConfig is expected to be one of the tryInterpretConstant in @b PolynomialNormalizerConfig
 */
template<Theory::Interpretation inter>
struct FunctionEvaluator {
  template<class PolynomialNormalizerConfig>
  static TermEvalResult evaluate(Term* orig, TermEvalResult* evaluatedArgs);
};


template<Theory::Interpretation inter>
struct PredicateEvaluator {
  template<class PolynomialNormalizerConfig>
  static LitEvalResult evaluate(Literal* orig, TermEvalResult* evaluatedArgs);
};

#include "Kernel/PolynomialNormalizer/FunctionEvaluator.hpp"
#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Implementation of literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config>
inline Literal* createLiteral(Literal* orig, TermEvalResult* evaluatedArgs) {
  auto arity = orig->arity();

  Stack<TermList> args(arity);
  for (int i = 0; i < arity; i++) {
    args.push(std::move(evaluatedArgs[i]).match<TermList>(
      [](TermList&& t) { return t;                            },
      [](AnyPoly&&  p) { return p.template toTerm_<Config>(); }
      ));
  }
  return Literal::create(orig, args.begin());
}


template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluate(Literal* lit) const {
  Stack<TermEvalResult> terms(lit->arity());
  for (int i = 0; i < lit->arity(); i++) {
    terms.push(evaluate(*lit->nthArgument(i)));
  }
  return evaluateStep(lit, terms.begin());
}

template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluateStep(Literal* orig, TermEvalResult* evaluatedArgs) const {
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
TermEvalResult evaluateConst(typename number::ConstantType c) {
  return TermEvalResult::template variant<1>(AnyPoly(Polynom<number>(c)));
}



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main term  evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


template<class Config> TermEvalResult PolynomialNormalizer<Config>::evaluate(TermList term) const {
  if (term.isTerm()) {
    return evaluate(term.term()); 
  } else {
    ASS_REP(term.isVar(), term);
    /* single variables can't be simplified */
    return TermEvalResult::variant<0>(term);
  }
}

template<class Config> TermEvalResult PolynomialNormalizer<Config>::evaluate(Term* term) const {
  struct Eval 
  {
    const PolynomialNormalizer& norm;
    TermEvalResult operator()(Variable v) 
    { return TermEvalResult(TermList::var(v.id())); }

    TermEvalResult operator()(Term* t, TermEvalResult* ts) 
    { return norm.evaluateStep(t, ts); }
  };

  static Memo::Hashed<Eval> memo;
  return evaluateBottomUp(term, Eval{ *this }, memo);
}


template<class Config>
inline TermList createTerm(unsigned fun, const Signature::Symbol& sym, TermEvalResult* evaluatedArgs) {
  Stack<TermList> args(sym.arity());

  auto& op = *sym.fnType();
  auto arity = op.arity();
  for (int i = 0; i < arity; i++) {
    args.push(std::move(evaluatedArgs[i]).match<TermList>(
        [](TermList&& t) {return t;}
      , [](AnyPoly&& p) { return p.template toTerm_<Config>(); }
        ));
  }
  return TermList(Term::create(fun, arity, args.begin()));
}


template<class Config> TermEvalResult PolynomialNormalizer<Config>::evaluateStep(Term* orig, TermEvalResult* args) const {
  CALL("PolynomialNormalizer::evaluateStep(Term* orig, TermEvalResult* args)")
  DEBUG("evaluating ", *orig)

#define HANDLE_CASE(INTER) case Interpretation::INTER: return FunctionEvaluator<Interpretation::INTER>::evaluate<Config>(orig, args); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return TermEvalResult::template variant<0>(createTerm<Config>(functor, *sym, args));


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
  return TermEvalResult::template variant<0>(createTerm<Config>(functor, *sym, args));
}



} // Kernel.hpp
#undef DEBUG


#endif // __POLYNOMIAL_NORMALIZER_HPP__
