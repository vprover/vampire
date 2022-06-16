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
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using namespace Lib;


namespace Inferences {

using LitSimplResult = SimplifyingGeneratingLiteralSimplification::Result;

PolynomialEvaluationRule::~PolynomialEvaluationRule() {}


PolynomialEvaluationRule::PolynomialEvaluationRule(Ordering& ordering) 
  : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering)
  // TODO we have an additional step of normalization here. simplify!
  , _inner(/* removeZeros */ true) {}


Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  CALL("createLiteral");

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
  CALL("PolynomialEvaluation::simplifyLiteral");

  Stack<PolyNf> terms(lit->numTermArguments());
  auto anyChange = false;
  for (unsigned i = 0; i < lit->numTermArguments(); i++) {
    auto term = lit->termArg(i);
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getTermArgSort(lit, i)));
    auto ev = _inner.evaluate(norm);
    anyChange = anyChange || ev.value.isSome();
    terms.push(std::move(ev).value || norm);
  }
  auto simplified = _inner.tryEvalPredicate(lit, terms.begin());
  anyChange = anyChange || simplified.isSome();

  return anyChange 
      ? std::move(simplified)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); })
      : LitSimplResult::literal(lit);
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

Option<LitSimplResult> PolynomialEvaluation::tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialEvaluation::tryEvalPredicate(Literal* term)")
  DEBUG("evaluating: ", orig->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return Option<LitSimplResult>();
#define HANDLE_NUM_CASES(NUM)                                                                                 \
      HANDLE_CASE(NUM ## _IS_INT)                                                                             \
      HANDLE_CASE(NUM ## _IS_RAT)                                                                             \
      HANDLE_CASE(NUM ## _IS_REAL)                                                                            \
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
}

#include "Inferences/FunctionEvaluation.cpp"


bool anyOverflow(MaybeOverflow<PolyNf>* polys, unsigned cnt) 
{ 
  for (unsigned i = 0; i < cnt; i++) 
    if (polys[i].overflowOccurred) 
      return true;  

  return false;
}

MaybeOverflow<Option<PolyNf>> trySimplify(FuncTerm const& orig, Theory::Interpretation i, MaybeOverflow<PolyNf>* evalArgs) 
{
  CALL("trySimplify(FuncTerm orig, Theory::Interpretation i, PolyNf* evalArgs) ")
  switch (i) {

#define CONSTANT_CASE_2(Num, func, expr)                                                                      \
    case Num##Traits:: func ## I:                                                                           \
      {                                                                                                     \
        using Const = typename Num##Traits::ConstantType;                                                   \
        return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
      }                                                                                                     \

#define CASE(inter)                                                                                           \
    case inter: return FunctionEvaluator<inter>::simplify(evalArgs);

#define QUOTIENT_REMAINDER_CASES(X)                                                                           \
    CASE(Theory::INT_QUOTIENT_  ## X)                                                                       \
    CASE(Theory::INT_REMAINDER_ ## X)

#define FRAC_CASE(Num)                                                                                        \
    CASE(Num##Traits::divI)

#define NUM_CASE(Num)                                                                                         \
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
      return maybeOverflow( none<PolyNf>(), anyOverflow(evalArgs, orig.numTermArguments()));
  }
}


MaybeOverflow<Option<PolyNf>> PolynomialEvaluation::evaluate(TermList term, SortId sort) const 
{ return evaluate(TypedTermList(term, sort)); }

MaybeOverflow<Option<PolyNf>> PolynomialEvaluation::evaluate(Term* term) const 
{ return evaluate(TypedTermList(term)); }

MaybeOverflow<Option<PolyNf>> PolynomialEvaluation::evaluate(TypedTermList term) const 
{ return evaluate(PolyNf::normalize(term)); }

template<class Number>
MaybeOverflow<Polynom<Number>> simplifyPoly(Polynom<Number> const& in, MaybeOverflow<PolyNf>* simplifiedArgs, bool removeZeros);

template<class Number>
MaybeOverflow<Monom<Number>> simplifyMonom(Monom<Number> const& in, MaybeOverflow<PolyNf>* simplifiedArgs, bool removeZeros);

MaybeOverflow<AnyPoly> simplifyPoly(AnyPoly const& p, MaybeOverflow<PolyNf>* ts, bool removeZeros)
{ return p.apply([&](auto& p) {
    return simplifyPoly(*p, ts, removeZeros)
      .map([](auto p) -> AnyPoly { return AnyPoly(perfect(std::move(p))); }); }); }

MaybeOverflow<Option<PolyNf>> PolynomialEvaluation::evaluate(PolyNf normalized) const 
{
  CALL("PolynomialEvaluation::evaluate(TypedTermList term) const")

  DEBUG("evaluating ", normalized)
  struct Eval 
  {
    const PolynomialEvaluation& norm;
    bool _removeZeros;

    using Result = MaybeOverflow<PolyNf>;
    using Arg    = PolyNf;

    MaybeOverflow<PolyNf> operator()(PolyNf orig, MaybeOverflow<PolyNf>* ts) 
    { 
      return orig.match(
          [&](Perfect<FuncTerm> f)  -> MaybeOverflow<PolyNf>
          { 
            auto itp = f->function().tryInterpret();
            auto simpl = itp.isSome() ?  trySimplify(*f, itp.unwrap(), ts)
                                      : maybeOverflow(none<PolyNf>(), anyOverflow(ts, f->numTermArguments()));

            return simpl.map([&](Option<PolyNf> x) -> PolyNf { 
                return x || [&]() {
                  Stack<PolyNf> args(f->numTermArguments());
                  for (unsigned i = 0; i < f->numTermArguments(); i++)
                    args.push(std::move(ts[i].value));
                  return PolyNf(perfect(FuncTerm(f->function(), std::move(args))));
                };
            });
          }, 

          [&](Variable v) 
          { return maybeOverflow(PolyNf(v), false); },

          [&](AnyPoly p) 
          { return simplifyPoly(p, ts, _removeZeros).map([](AnyPoly p) { return PolyNf(p); }); }
      );
    }
  };
  auto out = evaluateBottomUp(normalized, Eval{ *this, _removeZeros, }, _memo);
  return out.map([&normalized](PolyNf out) {
      return out == normalized ? Option<PolyNf>()
                               : Option<PolyNf>(std::move(out));
      });
}

// template<class Config>
// PolyNf createTerm(unsigned fun, PolyNf* evaluatedArgs) 
// { return perfect(FuncTerm(FuncId(fun), evaluatedArgs)); }

template<class Number>
MaybeOverflow<Polynom<Number>> PolynomialEvaluation::simplifySummation(Stack<Monom<Number>> summands, bool removeZeros)
{ 
  CALL("simplifySummation(Stack<Monom<Number>>, bool removeZeros)") 
  using Monom   = Monom<Number>;
  using Polynom = Polynom<Number>;

  bool overflow = false;
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
        try {
          numeral = numeral + summands[i+1].numeral;
        } catch (MachineArithmeticException&) {
          overflow = true;
          auto max = numeral;//std::max(numeral, summands[i+1].numeral);
          auto min = summands[i+1].numeral;
          try {
            if (min.abs() > max.abs()) {
              std::swap(min, max);
            }
          } catch (Kernel::MachineArithmeticException&) { 
            /* do nothing */
          }
          summands[offs++] = Monom(max, factors);
          numeral = min;
        }
        i++;
      }
      if (!removeZeros || numeral != Number::zeroC) 
        summands[offs++] = Monom(numeral, factors);
    }
    summands.truncate(offs);
  }

  auto poly = Polynom(std::move(summands));
  poly.integrity();
  return maybeOverflow(std::move(poly), overflow);
}

template MaybeOverflow<Polynom< IntTraits>> PolynomialEvaluation::simplifySummation< IntTraits>(Stack<Monom< IntTraits>> summands, bool removeZeros);
template MaybeOverflow<Polynom< RatTraits>> PolynomialEvaluation::simplifySummation< RatTraits>(Stack<Monom< RatTraits>> summands, bool removeZeros);
template MaybeOverflow<Polynom<RealTraits>> PolynomialEvaluation::simplifySummation<RealTraits>(Stack<Monom<RealTraits>> summands, bool removeZeros);



template<class Number>
MaybeOverflow<Polynom<Number>> simplifyPoly(Polynom<Number> const& in, MaybeOverflow<PolyNf>* simplifiedArgs, bool removeZeros)
{ 
  CALL("simplify(Polynom<Number>const&, PolyNf* simplifiedArgs)") 
  using Monom   = Monom<Number>;

  // first we simplify all the monoms containted in this polynom
  bool overflow = false;
  Stack<Monom> sum;
  {
    auto offs = 0;
    for (unsigned i = 0; i < in.nSummands(); i++) {
      auto monom  = in.summandAt(i);
      auto simpl_ = simplifyMonom(monom, &simplifiedArgs[offs], removeZeros);
      auto simpl = simpl_.value;
      // ASS(!simpl_.overflowOccurred || !simpl.isZero())
      if (simpl_.overflowOccurred)
        overflow = true;

      if (simpl.isZeroMul() && removeZeros) {
        /* we don't add it */
      } else if (simpl.factors->nFactors() == 1 && simpl.factors->factorAt(0).tryPolynom().isSome()) {
        /* k * (t1 + ... tn) ==> k * t1 + ... k * tn */
        auto origSize = sum.size(); 
        try {
          auto poly = simpl.factors->factorAt(0).tryPolynom().unwrap();
          for (auto fac : poly->iterSummands()) {
            fac.numeral = fac.numeral * simpl.numeral;
            ASS(!removeZeros || fac.numeral != Number::zeroC)
            sum.push(fac);
          }
        } catch (MachineArithmeticException&) {
          overflow = true;
          sum.truncate(origSize);
          sum.push(simpl);
        }
      } else {
        sum.push(simpl);
      }
      offs += monom.factors->nFactors();
    }
  }

  auto res = PolynomialEvaluation::simplifySummation(std::move(sum), removeZeros);
  if (overflow) {
    res.overflowOccurred = true;
  }
  return res;
}


/** Simplifies the factors of a monom. 
 * In exact this means, that all the numeral factors are collapsed into one numeral (e.g. 3*4*3*x ==> 36*x)
 */
template<class Number>
MaybeOverflow<Monom<Number>> simplifyMonom(Monom<Number> const& in, MaybeOverflow<PolyNf>* simplifiedArgs, bool removeZeros)
{ 

  using Numeral      = typename Number::ConstantType;
  using Monom        = Monom<Number>;
  using Polynom      = Polynom<Number>;
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

  bool overflow = false;

  auto& facs = *in.factors;
  Stack<MonomFactor> args(facs.nFactors());
  for (unsigned i = 0; i < facs.nFactors(); i++) {
    if (simplifiedArgs[i].overflowOccurred) 
      overflow = true; // TODO it might happen that the overflowed term is simplified away later on. we do not yet make up for this yet
    args.push(MonomFactor(simplifiedArgs[i].value, facs.factorAt(i).power));
  }

  std::sort(args.begin(), args.end());

  auto offs = 0;
  auto numeral = in.numeral;
  bool needsSorting = false;

  for (unsigned i = 0; i < facs.nFactors(); i++) {
    auto& arg = args[i];
    auto c = arg.term.template tryNumeral<Number>();
    if (c.isSome()) {
      // arg is a number constant
      try {
        auto num2 = pow(c.unwrap(), arg.power);
        try {
          numeral = numeral * num2;
        } catch (MachineArithmeticException&) {
          overflow = true;
          needsSorting = true;
          auto min = std::min(numeral, num2);
          auto max = std::max(numeral, num2);
          args[offs++] = MonomFactor(PolyNf(AnyPoly(perfect(Polynom(max)))), 1);
          numeral = min;
        }
      } catch (MachineArithmeticException&) {
        overflow = true;
        args[offs++] = arg;
      }
    } else {
      // arg is a non-number term
      auto term  = arg.term;
      auto power = arg.power;
      while (i + 1 < facs.nFactors() && args[i + 1].term == term) {
        power += args[i + 1].power;
        i++;
      }
      if (power != 0)
        args[offs++] = MonomFactor(term, power);
    }
  }
  args.truncate(offs);

  if (needsSorting) {
    std::sort(args.begin(), args.end());
  }

  if (numeral == Numeral(0) && removeZeros) {
    return maybeOverflow(Monom::zero(), false);
  } else {
    return maybeOverflow(Monom(numeral, perfect(MonomFactors(std::move(args)))), overflow); 
  }
}


TermList PolynomialEvaluation::evaluateToTerm(Term* in) const
{
  auto norm = PolyNf::normalize(in);
  auto eval = evaluate(in).value || norm;
  return eval.denormalize();
}

} // Inferences
