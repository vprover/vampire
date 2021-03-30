/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

namespace VariablePowerGeneralizationImpl {

/**
*  Rule 4)
*    generalize variable multiplication (REALS only)
*    C[X ⋅ X ⋅ ... ⋅ X ] 
*    ------------ 
*    C[X]
*    where 
*    - all occurences of X are in terms of the form `X ⋅ X ⋅ ... ⋅ X` 
*    - sound due to substitution { X -> X^(0/n) }
*    - obviously a generalization 
*/

using IntLattice = FlatMeetLattice<int>;
using PowerMap = Map<Variable, IntLattice>;
template<class Num>
using EnableIfNotReal = typename std::enable_if<!std::is_same<Num, RealTraits>::value, int>::type;

/** 
 * Polymorphic closure for preprocessing for the rule application.
 *
 * Collects for each variable the power in which it occurs or Bot when the variable occurs in different powers
 */
struct Preprocess 
{
  PowerMap &powers;

  void operator()(Perfect<Polynom<RealTraits>> p) 
  {
    for (auto summand : p->iterSummands()) {
      for (auto factor : summand.factors->iter()) {
        auto var = factor.term.tryVar();
        if (var.isSome()) {


          auto current = factor.power == 0 || factor.power == 1  /* <- power 0 should never happen. 
                                                                       power 1 yields a nop-generalization */
            ? IntLattice::bot()
            : IntLattice(factor.power);

          powers.updateOrInit(var.unwrap(),
              [&](IntLattice old) { return current.meet(old); },
              [&]() { return current; }
            );
        }
      }
    }
  }


  template<class Num, EnableIfNotReal<Num> = 0> 
  void operator()(Perfect<Polynom<Num>> p) 
  { }

};

struct Generalize 
{
  PowerMap& powers;
  bool doOrderingCheck;

  Monom<RealTraits> operator()(Monom<RealTraits> p, PolyNf* evaluatedArgs)  
  {
    unsigned i = 0;
    return Monom<RealTraits>(
        p.numeral, 
        perfect(MonomFactors<RealTraits>(
          p.factors->iter()
           .map([&](MonomFactor<RealTraits> m) 
             { 
                auto var = m.term.tryVar();
                if (var.isSome() && !powers.get(var.unwrap()).isBot()) {
                  ASS_EQ(evaluatedArgs[i], var.unwrap());
                  return MonomFactor<RealTraits>(evaluatedArgs[i++], 2 - ( m.power % 2 ));
                } else {
                  return MonomFactor<RealTraits>(evaluatedArgs[i++], m.power); 
                }
              })
           .template collect<Stack>())));
  }

  template<class Num, EnableIfNotReal<Num> = 0>
  Monom<Num> operator()(Monom<Num> p, PolyNf* evaluatedArgs)  
  { return Monom<Num>(p.numeral, perfect(p.factors->replaceTerms(evaluatedArgs))); }

};


/** 
 * applies the rule
 */ 
SimplifyingGeneratingInference1::Result applyRule(Clause* cl, bool doOrderingCheck) 
{
  DEBUG("input clause: ", *cl);
  PowerMap powers;

  /* preprocessing. finds all products `X ⋅ X ⋅ ... ⋅ X` such that the rule is applicable */
  for (auto poly : iterPolynoms(cl)) {
    poly.apply(Preprocess { powers, });
  }

  bool applicable = 
    iterTraits(powers.iter())
      .find([](PowerMap::Entry& e) { return !e.value().isBot() && e.value().unwrap() >= 3; })
      .isSome();

  DEBUG("generalizations: ", powers);

  if (applicable) {
    return generalizeBottomUp(cl, EvaluateMonom<Generalize> { Generalize { powers, doOrderingCheck } });
  } else {
    return SimplifyingGeneratingInference1::Result::nop(cl);
  }
}


} // namespace VariablePowerGeneralizationImpl


