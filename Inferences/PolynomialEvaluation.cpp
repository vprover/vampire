#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
using namespace Lib;


namespace Inferences {

using LitSimplResult = SimplifyingGeneratingLiteralSimplification::Result;

PolynomialEvaluation::~PolynomialEvaluation() {}

PolynomialEvaluation::PolynomialEvaluation(Ordering& ordering) : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering) {}


Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
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

PolynomialEvaluation::Result PolynomialEvaluation::simplifyLiteral(Literal* lit) 
{
  Stack<PolyNf> terms(lit->arity());
  auto anyChange = false;
  for (int i = 0; i < lit->arity(); i++) {
    auto term = *lit->nthArgument(i);
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getArgSort(lit, i)));
    auto ev = evaluate(norm);
    anyChange = anyChange || ev.isSome();
    terms.push(std::move(ev).unwrapOrElse([&](){ return norm; }));
  }
  auto simplified = evaluateStep(lit, terms.begin());
  anyChange = anyChange || simplified.isSome();

  return anyChange 
      ? std::move(simplified)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); })
      : LitSimplResult::literal(lit);
}

template<Theory::Interpretation inter>
struct PredicateEvaluator;

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"


Optional<LitSimplResult> PolynomialEvaluation::evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialEvaluation::evaluateStep(Literal* term)")
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

template<class Number>
Optional<PolyNf> trySimplifyUnaryMinus(PolyNf* evalArgs)
{
  CALL("trySimplifyUnaryMinus(PolyNf*)")
  // using Const = typename Number::ConstantType;
  return some<PolyNf>(PolyNf(AnyPoly(unique(
          evalArgs[0].template wrapPoly<Number>()->flipSign()
            ))));
}

template<class Number, class Clsr>
Optional<PolyNf> trySimplifyConst2(PolyNf* evalArgs, Clsr f) 
{
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (lhs.isSome() && rhs.isSome()) {
    return some<PolyNf>(PolyNf(AnyPoly(unique(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

Optional<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
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


Optional<PolyNf> PolynomialEvaluation::evaluate(TermList term, unsigned sortNumber) const 
{ return evaluate(TypedTermList(term, sortNumber)); }

Optional<PolyNf> PolynomialEvaluation::evaluate(Term* term) const 
{ return evaluate(TypedTermList(term)); }

Optional<PolyNf> PolynomialEvaluation::evaluate(TypedTermList term) const 
{ return evaluate(PolyNf::normalize(term)); }

Optional<PolyNf> PolynomialEvaluation::evaluate(PolyNf normalized) const 
{
  CALL("PolynomialEvaluation::evaluate(TypedTermList term) const")

  // auto norm = PolyNf::normalize(term);
  DEBUG("evaluating ", normalized)
  struct Eval 
  {
    const PolynomialEvaluation& norm;

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
PolyNf createTerm(unsigned fun, PolyNf* evaluatedArgs) 
{ return unique(FuncTerm(FuncId(fun), evaluatedArgs)); }





} // Inferences
