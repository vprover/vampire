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

struct Preprocess 
{
  NumeralMap& numerals;

  bool canDivideBy(IntegerConstantType i) 
  { return i == IntegerConstantType(1) || i == IntegerConstantType(-1); }

  bool canDivideBy(RationalConstantType i) 
  { return i != RationalConstantType(0); }

  bool canDivideBy(RealConstantType i) 
  { return i != RealConstantType(0); }

  template<class NumTraits> 
  void operator()(Perfect<Polynom<NumTraits>> poly)
  {
    CALL("Preprocess::operator()")

    for (auto monom : poly->iterSummands()) {
      for (auto factor : monom.factors->iter()) {
        
        auto v = factor.term.tryVar();
        if (v.isSome()) {
          auto numeral = FlatMeetLattice<AnyNumber<Numeral>>(AnyNumber<Numeral>(monom.numeral));
          if (factor.power == 1 && canDivideBy(monom.numeral)) {
            numerals.updateOrInit(v.unwrap(), 
                /* update function */
                [&](FlatMeetLattice<AnyNumber<Numeral>> n) 
                { return n.meet(numeral); },
                /* init function */
                [&]() { return numeral; });
          } else {
            ASS_NEQ(factor.power, 0)
            numerals.replaceOrInsert(v.unwrap(), FlatMeetLattice<AnyNumber<Numeral>>::bot());
          }
        }
      }
    }
  }
};


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

struct IsOne {
  template<class C> 
  bool operator()(C numeral) const 
  { return C(1) == numeral; }
};


/** applies the rule */ 
SimplifyingGeneratingInference1::Result applyRule(Clause* cl, bool doOrderingCheck) 
{
  DEBUG("input clause: ", *cl);

  NumeralMap numerals;

  for (auto poly : iterPolynoms(cl)) {
    poly.apply(Preprocess {numerals});
  }

  Option<typename NumeralMap::Entry &> selected;
  for (auto& e : iterTraits(numerals.iter()) ) {
    FlatMeetLattice<AnyNumber<Numeral>> num = e.value();
    if (!num.isBot() && !num.unwrap().apply(IsOne{})) {
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
