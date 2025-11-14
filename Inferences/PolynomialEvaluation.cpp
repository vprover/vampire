/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using namespace Lib;


namespace Inferences {

using LitSimplResult = SimplifyingGeneratingLiteralSimplification::Result;

PolynomialEvaluationRule::~PolynomialEvaluationRule() {}


PolynomialEvaluationRule::PolynomialEvaluationRule(Ordering& ordering) 
  : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering)
  // TODO we have an additional step of normalization here. simplify!
  , _alwaysEvaluate(env.options->alasca())
  {}


Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  if (orig->isEquality()) {
    return Literal::createEquality(
          orig->polarity(), 
          evaluatedArgs[0].denormalize(), 
          evaluatedArgs[1].denormalize(), 
          SortHelper::getTermArgSort(orig, 0));
  } else {
    auto termArgs = orig->numTermArguments();
    auto typeArgs = orig->numTypeArguments();
    Stack<TermList> args(typeArgs + termArgs);
    for (unsigned i = 0; i < typeArgs; i++) {
      args.push(orig->typeArg(i));
    }
    for (unsigned i = 0; i < termArgs; i++) {
      args.push(evaluatedArgs[i].denormalize());
    }
    return Literal::create(orig, args.begin());
  }
}

PolynomialEvaluationRule::Result PolynomialEvaluationRule::simplifyLiteral(Literal* lit) 
{
  TIME_TRACE("polynomial evaluation");

  Stack<PolyNf> terms(lit->numTermArguments());
  auto anyChange = false;
  for (unsigned i = 0; i < lit->numTermArguments(); i++) {
    auto term = lit->termArg(i);
    bool simplified;
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getTermArgSort(lit, i)), simplified);
    auto ev = _inner.evaluate(norm);
    anyChange = anyChange || ev.isSome() || simplified;
    terms.push(std::move(ev) || norm);
  }
  auto simplified = _inner.tryEvalPredicate(lit, terms.begin());
  anyChange = anyChange || simplified.isSome();

  return anyChange || _alwaysEvaluate
      ? std::move(simplified)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); })
      : LitSimplResult::literal(lit);
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

Option<LitSimplResult> PolynomialEvaluation::tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const {
  auto impl = [&]() {


#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return Option<LitSimplResult>();
#define HANDLE_NUM_CASES(NUM)                                                             \
      HANDLE_CASE(NUM ## _IS_INT)                                                         \
      HANDLE_CASE(NUM ## _IS_RAT)                                                         \
      HANDLE_CASE(NUM ## _IS_REAL)                                                        \
      HANDLE_CASE(NUM ## _GREATER)                                                        \
      HANDLE_CASE(NUM ## _GREATER_EQUAL)                                                  \
      HANDLE_CASE(NUM ## _LESS)                                                           \
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
      case Interpretation::ARRAY_BOOL_SELECT:
        return Option<LitSimplResult>();

      case ANY_INTERPRETED_FUNCTION: 
      case Kernel::Theory::INVALID_INTERPRETATION: 
        ASSERTION_VIOLATION_REP(inter)
    }
    WARN("unexpected interpreted predicate: ", *orig, " (inter: ", inter, ")")
    ASSERTION_VIOLATION
    return Option<LitSimplResult>();
  } else {
    return Option<LitSimplResult>();
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES

  };
  auto out = impl();
  DEBUG("evaluated: ", orig->toString(), " ==> ", out);
  return out;
}

#include "Inferences/FunctionEvaluation.hpp"


Option<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
{
  try {
    switch (i) {

#define CONSTANT_CASE_2(Num, func, expr)                                                  \
    case Num##Traits:: func ## I:                                                         \
      {                                                                                   \
        using Const = typename Num##Traits::ConstantType;                                 \
        return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
      }                                                                                   \

#define CASE(inter)                                                                       \
    case inter: return FunctionEvaluator<inter>::simplify(evalArgs);

#define QUOTIENT_REMAINDER_CASES(X)                                                       \
    CASE(Theory::INT_QUOTIENT_  ## X)                                                     \
    CASE(Theory::INT_REMAINDER_ ## X)

#define FRAC_CASE(Num)                                                                    \
    CASE(Num##Traits::divI)                                                               \
    CASE(Num##Traits::floorI)                                                             \

#define NUM_CASE(Num)                                                                     \
    case Num ## Traits::minusI: return trySimplifyUnaryMinus<Num ## Traits>(evalArgs);

    NUM_CASE(Int)
    NUM_CASE(Rat)
    NUM_CASE(Real)
    QUOTIENT_REMAINDER_CASES(E)
    QUOTIENT_REMAINDER_CASES(T)
    QUOTIENT_REMAINDER_CASES(F)

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
  } catch (DivByZeroException&) {
    return none<PolyNf>();
  }
}


Option<PolyNf> PolynomialEvaluation::evaluate(TermList term, SortId sort) const 
{ return evaluate(TypedTermList(term, sort)); }

Option<PolyNf> PolynomialEvaluation::evaluate(Term* term) const 
{ return evaluate(TypedTermList(term)); }

Option<PolyNf> PolynomialEvaluation::evaluate(TypedTermList term) const 
{ return evaluate(PolyNf::normalize(term)); }

template<class Number>
PolyNf simplifyPoly(Polynom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros);

template<class Number>
Monom<Number> simplifyMonom(Monom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros);

PolyNf simplifyPoly(AnyPoly const& p, PolyNf* ts, bool removeZeros)
{ return p.apply([&](auto& p) {
    return simplifyPoly(*p, ts, removeZeros); }); }

Option<PolyNf> PolynomialEvaluation::evaluate(PolyNf normalized) const 
{
  static MemoNonVars<PolyNf, PolyNf> memo;
  auto out = BottomUpEvaluation<PolyNf, PolyNf>()
    .function(
        [&](PolyNf orig, PolyNf* ts) -> PolyNf 
        { 
          return orig.match(
              [&](Perfect<FuncTerm> f)
              { 
                return f->function().tryInterpret()
                  .andThen( [&](Theory::Interpretation && i)  -> Option<PolyNf>
                    { return trySimplify(i, ts); })
                  .unwrapOrElse([&]() -> PolyNf
                    { return PolyNf(perfect(FuncTerm(f->function(), ts))); });

              }, 

              [&](Variable v) 
              { return PolyNf(v); },

              [&](AnyPoly p) 
              { return PolyNf(simplifyPoly(p, ts, /*removeZeros=*/true)); }
          );
        })
    .memo<decltype(memo)&>(memo)
    .apply(normalized);
  auto outOpt = someIf(out != normalized, [&]() { return out; });
  DEBUG("evaluated ", normalized, " ==> ", outOpt)
  return outOpt;
}

template<class Number>
PolyNf PolynomialEvaluation::simplifySummation(Stack<Monom<Number>> summands, bool removeZeros)
{ 
  using Monom   = Monom<Number>;
  using Polynom = Polynom<Number>;

  // then we sort them by their monom, in order to add up the coefficients efficiently
  std::sort(summands.begin(), summands.end());

  // add up the coefficients (in place)
  {
    auto offs = 0;
    for (unsigned i = 0; i < summands.size(); i++) { 
      auto monom = summands[i];
      auto numeral = monom.numeral;
      auto factors = monom.factors;
      while ( i + 1 < summands.size() && summands[i+1].factors == factors ) {
        numeral = numeral + summands[i+1].numeral;
        i++;
      }
      if (!removeZeros || numeral != Number::constant(0)) 
        summands[offs++] = Monom(numeral, factors);
    }
    summands.truncate(offs);
  }

  if (summands.size() == 1 
      && summands[0].numeral == 1
      && summands[0].factors->nFactors() == 1
      && summands[0].factors->factorAt(0).power == 1
      ) {
    return summands[0].factors->factorAt(0).term;
  } else {
    auto poly = Polynom(std::move(summands));
    poly.integrity();
    return PolyNf(AnyPoly(perfect(std::move(poly))));
  }
}

template PolyNf PolynomialEvaluation::simplifySummation< IntTraits>(Stack<Monom< IntTraits>> summands, bool removeZeros);
template PolyNf PolynomialEvaluation::simplifySummation< RatTraits>(Stack<Monom< RatTraits>> summands, bool removeZeros);
template PolyNf PolynomialEvaluation::simplifySummation<RealTraits>(Stack<Monom<RealTraits>> summands, bool removeZeros);



template<class Number>
PolyNf simplifyPoly(Polynom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros)
{
  using Monom   = Monom<Number>;


  // first we simplify all the monoms contained in this polynom
  Stack<Monom> sum;
  {
    auto offs = 0;
    for (unsigned i = 0; i < in.nSummands(); i++) {
      auto monom  = in.summandAt(i);
      auto simpl = simplifyMonom(monom, &simplifiedArgs[offs], removeZeros);

      if (simpl.isZeroMul() && removeZeros) {
        /* we don't add it */
      } else if (simpl.factors->nFactors() == 1 && simpl.factors->factorAt(0).tryPolynom().isSome()) {
        /* k * (t1 + ... tn) ==> k * t1 + ... k * tn */
        auto poly = simpl.factors->factorAt(0).tryPolynom().unwrap();
        for (auto fac : poly->iterSummands()) {
          fac.numeral = fac.numeral * simpl.numeral;
          ASS(!removeZeros || fac.numeral != Number::constant(0))
          sum.push(fac);
        }
      } else {
        sum.push(simpl);
      }
      offs += monom.factors->nFactors();
    }
  }

  return PolynomialEvaluation::simplifySummation(std::move(sum), removeZeros);
}


/** Simplifies the factors of a monom. 
 * In exact this means, that all the numeral factors are collapsed into one numeral (e.g. 3*4*3*x ==> 36*x)
 */
template<class Number>
Monom<Number> simplifyMonom(Monom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros)
{ 

  using Numeral      = typename Number::ConstantType;
  using Monom        = Monom<Number>;
  using MonomFactor  = MonomFactor<Number>;
  using MonomFactors = MonomFactors<Number>;

  auto pow = [](Numeral c, int power) -> Numeral {
    ASS(power > 0)
    auto out = c;
    while (--power > 0) {
      out = out * c;
    }
    return out;
  };

  
  auto& facs = *in.factors;
  auto numeral = in.numeral;
  Stack<MonomFactor> args(facs.nFactors());
  for (unsigned i = 0; i < facs.nFactors(); i++) {
    auto power = facs.factorAt(i).power;
    if (auto poly_ = simplifiedArgs[i].downcast<Number>()) {
      auto& poly = **poly_;
      if (poly.nSummands() == 1) {
        numeral *= pow(poly.summandAt(0).numeral, power);
        args.loadFromIterator(
            poly.summandAt(0).factors->iter()
            .map([&](auto fac) { fac.power *= power; return fac; }));
        continue;
      }
    }
    args.push(MonomFactor(simplifiedArgs[i], power));
  }

  std::sort(args.begin(), args.end());

  auto offs = 0;
  bool needsSorting = false;

  for (unsigned i = 0; i < args.size(); i++) {
    auto& arg = args[i];
    auto c = arg.term.template tryNumeral<Number>();
    if (c.isSome()) {
      // arg is a number constant
      auto num2 = pow(c.unwrap(), arg.power);
      numeral = numeral * num2;
    } else {
      // arg is a non-number term
      auto term  = arg.term;
      auto power = arg.power;
      while (i + 1 < args.size() && args[i + 1].term == term) {
        power += args[i + 1].power;
        i++;
      }
      if (power != 0) {
        args[offs++] = MonomFactor(term, power);
      }
    }
  }
  args.truncate(offs);

  if (needsSorting) {
    std::sort(args.begin(), args.end());
  }

  if (numeral == Numeral(0) && removeZeros) {
    return Monom::zero();
  } else {
    return Monom(numeral, perfect(MonomFactors(std::move(args))));
  }
}


TermList PolynomialEvaluation::evaluateToTerm(Term* in) const
{
  auto norm = PolyNf::normalize(in);
  auto eval = evaluate(in) || norm;
  return eval.denormalize();
}

} // Inferences
