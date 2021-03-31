/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

namespace NumeralMultiplicationGeneralizationImpl 
{

/**
 * Rule 1)
 *   generalize multiplication
 *   C[k * X] 
 *   ------------ 
 *   C[X]
 *   where 
 *   - k is a non-zero number term
 *   - all occurences of X are in terms of the form `k * X`
 *   - sound due to substitution X -> (1/k) * X
 *   - generalization since obviously
 */
template<class NumTraits>
using Numeral = typename NumTraits::ConstantType;
using NumeralMap = Map<Variable, FlatMeetLattice<AnyNumber<Numeral>>>;

bool canDivideBy(IntegerConstantType i) 
{ return i == IntegerConstantType(1) || i == IntegerConstantType(-1); }

bool canDivideBy(RationalConstantType i) 
{ return i != RationalConstantType(0); }

bool canDivideBy(RealConstantType i) 
{ return i != RealConstantType(0); }

/** 
 * A polymorphic closure to bottom-up evaluate clause bottom-up that replaces all occurences of the factors in the field `toRem`
 */
struct Generalize 
{
  Variable var;
  AnyNumber<Numeral> num;
  bool doOrderingCheck;

  template<class NumTraits>
  Monom<NumTraits> operator()(Monom<NumTraits> monom, PolyNf* evaluatedArgs)  
  {
    CALL("NumeralMultiplicationGeneralizationImpl::Generalize::operator()")
    using Monom = Monom<NumTraits>;
    auto newFactors = perfect(monom.factors->replaceTerms(evaluatedArgs));
    for (auto f : monom.factors->iter()) {
      if (f.tryVar() == Option<Variable>(var)) {
        ASS_EQ(num.downcast<NumTraits>().unwrap(), monom.numeral)
        return Monom(Numeral<NumTraits>(1), newFactors);
      }
    }
    return Monom(monom.numeral, newFactors);
  }
};

const auto isOne = [](auto x) { return decltype(x)(1) == x; };

/** applies the rule */ 
SimplifyingGeneratingInference1::Result applyRule(Clause* cl, bool doOrderingCheck) 
{
  DEBUG("input clause: ", *cl);

  NumeralMap numerals;

  /* scan candidate numeral multiplications n * x  */
  for (auto poly : iterPolynoms(cl)) {
    poly.apply([&](auto& poly) {
      for (auto monom : poly->iterSummands()) {
        for (auto factor : monom.factors->iter()) {
          
          auto var = factor.term.tryVar();
          if (var.isSome()) {
            auto numeral = FlatMeetLattice<AnyNumber<Numeral>>(AnyNumber<Numeral>(monom.numeral));

            if (factor.power == 1 && canDivideBy(monom.numeral)) {
              /* we found numeral * var */
              numerals.updateOrInit(var.unwrap(), 
                  /* update the numeral if there was already one associated with this variable */
                  [&](auto n) 
                  { return n.meet(numeral); },
                  /* init the numeral if there was none */
                  [&]() { return numeral; });
            } else {
              ASS_NEQ(factor.power, 0)
              /* x^n ==> we cannot generalize. hence we set the numeral for this variable to bottom. */
              numerals.replaceOrInsert(var.unwrap(), FlatMeetLattice<AnyNumber<Numeral>>::bot());
            }
          }
        }
      }
    });
  }

  /* select one of the variables we can generalize on */
  Option<typename NumeralMap::Entry &> selected;
  for (auto& e : iterTraits(numerals.iter()) ) {
    FlatMeetLattice<AnyNumber<Numeral>> num = e.value();
    if (!num.isBot() && !num.unwrap().apply(isOne)) {
      /* we use the entry with the least variable, in order to prevent non-determinism */
      if (selected.isNone() || e.key() < selected.unwrap().key()) {
        selected = decltype(selected)(e);
      }
    }
  }

  if (selected.isNone()) {
    DEBUG("not applicable")
    return SimplifyingGeneratingInference1::Result::nop(cl);
  } else {
    auto& e = selected.unwrap();
    DEBUG("selected generalization: (", e.key(), ", ", e.value(), ")");
    Generalize gen { e.key(), e.value().unwrap(), doOrderingCheck };
    return generalizeBottomUp(cl, EvaluateMonom<Generalize> {gen});
  }
}

} // namespace NumeralMultiplicationGeneralizationImpl
