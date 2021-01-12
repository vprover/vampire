/*
 * File NonZeroMultiplicationGeneralizationImpl.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

namespace NonZeroMultiplicationGeneralizationImpl {

/**
 * Rule' 2)
 *   generalize addition
 *   C[X + d] 
 *   ------------ 
 *   C[X]
 *   where 
 *   - all occurences of X are in terms of the form `X + d`
 *   - sound due to substitution X -> X - d
 *   - generalization since obviously
 */

template<class NumTraits> class FactorSet;

using GenMap = Map<Variable, AnyNumber<FactorSet>>;

template<class NumTraits>
class FactorSet 
{
  using Monom = Kernel::Monom<NumTraits>;
  using Const = typename NumTraits::ConstantType;
  using MonomFactors = Kernel::MonomFactors<NumTraits>;

  Stack<Monom> _cancellable;

  FactorSet(decltype(_cancellable) cancel) : _cancellable(cancel) {}

public:
  using Lattice = FactorSet;
  FactorSet& operator=(FactorSet&&) = default;
  FactorSet(FactorSet&&) = default;

  static FactorSet bot() 
  { return FactorSet(decltype(_cancellable){}); }

  FactorSet(Variable var, Monom const& monom) : FactorSet(decltype(_cancellable)()) 
  {
    _cancellable.reserve(monom.factors->nFactors() - 1);
    for (auto const& factor : monom.factors->iter()) {
      if (factor.tryVar() != some(var)) {
        _cancellable.push(monom);
      }
    }
  }

  FactorSet intersect(FactorSet&& rhs) && {
    CALL("FactorSet::intersect")
    auto& lhs = *this;
    return FactorSet(intersectSortedStack(std::move(lhs._cancellable), std::move(rhs._cancellable)));
  }

  Stack<Monom> const& factors() const 
  { return _cancellable; }

  bool isBot() const 
  { return _cancellable.isEmpty(); }

  friend ostream& operator<<(ostream& out, FactorSet const& self)
  { return out << self._cancellable; }
};


struct Preprocess 
{
  GenMap& map;

  template<class NumTraits> 
  void operator()(Perfect<Polynom<NumTraits>> poly)
  {
    CALL("NonZeroMultiplicationGeneralizationImpl::Preprocess::operator()")

    // a variable might occur twice within one sum.
    Set<Variable> didOccur;
    for (auto monom : poly->iterSummands()) {
      for (auto factor : monom.factors->iter()) { 
        auto var = factor.tryVar();

        if (var.isSome()) {
          auto v = var.unwrap();
          auto gen = FactorSet<NumTraits>(v, monom);
          map.updateOrInit(v,
              [&](AnyNumber<FactorSet> old_) 
              { 
                auto old = old_.downcast<NumTraits>().unwrap();
                auto result = move(old).intersect(move(gen));
                return AnyNumber<FactorSet>(move(result)); 
              },
              [&]() { return AnyNumber<FactorSet>(move(gen)); });
        }

      }
    }
  }
};


struct IsBot 
{
  template<class C>
  bool operator()(C const& lattice)
  { return lattice.isBot(); }
};

struct AnyGround {
  template<class NumTraits>
  bool operator()(FactorSet<NumTraits>const& set) {
    for (auto const& factor : set.factors()) {
      if (factor.ground()) return true;
    }
    return false;
  }
};


/** applies the rule */ 
SimplifyingGeneratingInference1::Result applyRule(Clause* cl, bool doOrderingCheck) 
{
  DEBUG("input clause: ", *cl);

  GenMap map;

  for (auto poly : iterPolynoms(cl)) {
    poly.apply(Preprocess {map});
  }

  Option<typename GenMap::Entry &> selected;
  for (auto& e : iterTraits(map.iter()) ) {
    if (!e.value().apply(IsBot{})) {
      /* we use the entry with the least variable, in order to prevent non-determinism */
      if (selected.isNone() || e.key() < selected.unwrap().key()) {
        selected = decltype(selected)(e);
      }
    }
  }

  if (selected.isNone()) {
    DEBUG("not applicable")
    // return SimplifyingGeneratingInference1::Result::nop(cl);
  } else {

    auto& e = selected.unwrap();
    DEBUG("selected generalization: ", e.key(), " ", e.value());

    NON_ZERO_FAIL(Asg, e.value().apply(AnyGround{}));
    // Generalize gen { e.key(), e.value(), doOrderingCheck };
    // return generalizeBottomUp(cl, EvaluateMonom<Generalize> {gen});
  }
  return SimplifyingGeneratingInference1::Result::nop(cl);

}

} // namespace NonZeroMultiplicationGeneralizationImpl
