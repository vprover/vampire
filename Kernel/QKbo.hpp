/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file QKbo.hpp
 *
 * Defines a Knuth-Bendix Ordering for linear arithmetic. This ignores numeral multiplications,
 * (i.e. it considers terms t and nt where n is a numeral as equivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __QKBO__
#define __QKBO__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Kernel/ALASCA.hpp"

#include "Ordering.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/OrderingUtils.hpp"

// TODO namespacing ALASCA
namespace Kernel {

struct SignedTerm
{
  Sign sign;
  TermList term;

  static SignedTerm pos(TermList t)
  { return { .sign = Sign::Pos, .term = t, }; }

  static SignedTerm neg(TermList t)
  { return { .sign = Sign::Neg, .term = t, }; }

  static SignedTerm zero(TermList t)
  { return { .sign = Sign::Zero, .term = t, }; }

  friend std::ostream& operator<<(std::ostream& out, SignedTerm const& self)
  { return out << self.sign << self.term; }

  friend bool operator==(SignedTerm const& lhs, SignedTerm const& rhs)
  { return lhs.sign == rhs.sign && lhs.term == rhs.term; }

  friend bool operator!=(SignedTerm const& lhs, SignedTerm const& rhs)
  { return !(lhs == rhs); }

  friend bool operator<(SignedTerm const& l, SignedTerm const& r)
  { return std::tie(l.term, l.sign) < std::tie(r.term, r.sign); }

  friend bool operator> (SignedTerm const& l, SignedTerm const& r) { return r < l; }
  friend bool operator<=(SignedTerm const& l, SignedTerm const& r) { return l == r || l < r; }
  friend bool operator>=(SignedTerm const& l, SignedTerm const& r) { return l == r || l > r; }
};

using SignedAtoms = WeightedMultiSet<SignedTerm>;


using namespace Lib;

class QKbo
  : public Ordering
{
  std::shared_ptr<InequalityNormalizer> _norm;
  KBO _kbo;
public:
  USE_ALLOCATOR(QKbo);

  QKbo(QKbo&& kbo) = default;
  QKbo& operator=(QKbo&& kbo) = default;
  explicit QKbo(KBO kbo, std::shared_ptr<InequalityNormalizer> norm);

  QKbo(Problem& prb, const Options& opts)
    : QKbo(KBO(prb, opts, /* qkboPrecedence */ true), InequalityNormalizer::global()) {}

  ~QKbo() override {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final ;

  void show(std::ostream& out) const final ;

private:
  auto& norm() const { return *_norm; }

  auto asClosure() const
  { return [this](auto const& l, auto const& r) { return this->compare(l, r); }; }

public:
  template<class NumTraits>
  Recycled<MultiSet<TermList>> nfEquality(Literal* l) const
  {
    ASS(l->isEquality())
    using Num = typename NumTraits::ConstantType;
    auto norm = this->norm().template normalize<NumTraits>(l).unwrap();
    Recycled<MultiSet<TermList>> out;
    out->init(
      NumTraits::sum(
          iterTraits(norm.term().iterSummands())
            .filter([](auto x) { return x.numeral >= Num(0);  })
            .map([](auto x) { return x.denormalize(); })),
      NumTraits::sum(iterTraits(norm.term().iterSummands())
          .filter([](auto x) { return x.numeral <= Num(0);  })
          .map([](auto x) { return (-x).denormalize(); })));
    return out;

  }


  static constexpr uint8_t POS_EQ_LEVEL = 0;
  static constexpr uint8_t NEG_EQ_LEVEL = 1;
  static constexpr uint8_t INEQ_LEVEL = 1;
  static constexpr uint8_t POS_IS_INT_LEVEL = 2;
  static constexpr uint8_t NEG_IS_INT_LEVEL = 3;

  using AtomsWithLvl = std::tuple<Recycled<SignedAtoms>, uint8_t>;


  template<class NumTraits>
  // the signs are not used here, but only there since we reuse code from signedAtoms and don't want to copy the datastructure.
  Option<AtomsWithLvl> atomsWithLvl(Literal* literal) const
  {
    using ASig = AlascaSignature<NumTraits>;
    ASS(AlascaState::interpretedPred(literal))
    TermList term;
    uint8_t level;
    auto f = literal->functor();
    if (literal->isEquality() || f == NumTraits::geqF() || f == NumTraits::greaterF()) {
      auto mainIdx = literal->isEquality() && literal->termArg(0) == NumTraits::zero() ? 1 : 0;

      term = ASig::zero() == literal->termArg(1 - mainIdx) 
           ? literal->termArg(mainIdx)
           : NumTraits::add(literal->termArg(0), NumTraits::minus(literal->termArg(1)));

      level = literal->isEquality() 
        ? (literal->isPositive() ? POS_EQ_LEVEL : NEG_EQ_LEVEL)
        :  INEQ_LEVEL;
    } else {
      ASS(f == NumTraits::isIntF());
      term = literal->termArg(0);
      level = literal->isPositive() ? POS_IS_INT_LEVEL : NEG_IS_INT_LEVEL;
    }

    return signedAtoms<NumTraits>(term)
      .map([level](auto atoms) {
          return std::make_tuple(std::move(atoms), level);
      });
  }

  std::tuple<IntegerConstantType, Perfect<Polynom<IntTraits>>> divNf(Perfect<Polynom<IntTraits>> t) const
  { return std::make_tuple(IntegerConstantType(1), t); }

  template<class NumTraits>
  std::tuple<IntegerConstantType, Perfect<Polynom<NumTraits>>> divNf(Perfect<Polynom<NumTraits>> t) const
  {
    auto l = t->iterSummands()
      .map([](auto s) { return s.numeral.denominator(); })
      .fold(IntegerConstantType(1), [&](auto acc, auto next)
               { return acc.lcm(next); });
    return std::make_tuple(l.abs(), typename NumTraits::ConstantType(l, IntegerConstantType(1)) * t);
  }

  template<class NumTraits>
  Option<Recycled<SignedAtoms>> signedAtoms(TermList t) const
  {
    auto n = norm().normalize(TypedTermList(t, NumTraits::sort())).template wrapPoly<NumTraits>();
    auto atoms = rmNum(divNf(n));
    if (hasSubstitutionProperty(*atoms)) {
      return Option<decltype(atoms)>(std::move(atoms));
    } else {
      return Option<decltype(atoms)>();
    }
  }

  bool hasSubstitutionProperty(SignedAtoms const& l) const;

  template<class NumTraits>
  Recycled<WeightedMultiSet<SignedTerm>> rmNum(std::tuple<IntegerConstantType, Perfect<Polynom<NumTraits>>> t) const
  {
    Recycled<WeightedMultiSet<SignedTerm>> out;

    out->elems.raw().loadFromIterator(
        std::get<1>(t)->iterSummands()
              .map([](auto s) {
                auto count  = ifOfType<IntegerConstantType>(s.numeral,
                               [&](IntegerConstantType num) { return num; },
                                /* decltype(num) in { RatTraits, RealTraits } */
                               [&](auto num) {
                                 ASS_EQ(num.denominator(), IntegerConstantType(1))
                                 return num.numerator();
                               }).abs();
                if (count == IntegerConstantType(0)) {
                  ASS(s.numeral.sign() == Sign::Zero)
                  count = IntegerConstantType(1);
                }
                SignedTerm term = {
                  .sign = s.numeral.sign(),
                  .term = s.factors->denormalize(),
                };
                return std::make_tuple(term, count);
              })
        );
    std::sort(out->elems.raw().begin(), out->elems.raw().end(), [](auto& l, auto& r) { return std::get<0>(l) < std::get<0>(r); });
    out->weight = std::get<0>(t);
    out->elems.integrity();
    return out;
  }


  Option<AtomsWithLvl> atomsWithLvl(Literal* literal) const
  {
    using Out = Option<AtomsWithLvl>;
    return tryNumTraits([&](auto numTraits) {
      using NumTraits = decltype(numTraits);
      auto srt =  SortHelper::getTermArgSort(literal, 0);
      if (NumTraits::sort() != srt) {
        return Option<Out>();
      } else {
        return Option<Out>(atomsWithLvl<NumTraits>(literal));
      }
    }) || [&]() -> Out {
      ASS(literal->isEquality())
      auto level = literal->isPositive() ? POS_EQ_LEVEL : NEG_EQ_LEVEL;
      Recycled<WeightedMultiSet<SignedTerm>> multiset;
      multiset->elems.init(
        // the sign is only a dummy here to match the type of atomsWithLvl<NumTraits>
          SignedTerm::zero(literal->termArg(0)),
          SignedTerm::zero(literal->termArg(1)));
      return Option<AtomsWithLvl>(std::make_tuple(std::move(multiset), level));
    };
  }

  // TODO optimize?
  Result compare(AppliedTerm t1, AppliedTerm t2) const override
  { return compare(t1.apply(), t2.apply()); }

private:

  Result cmpNonAbstr(TermList, TermList) const;
  Option<TermList> abstr(TermList) const;

};

} // namespace Kernel

#endif // __QKBO__
