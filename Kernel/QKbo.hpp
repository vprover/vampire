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
 * (i.e. it considers terms t and nt where n is a numeral as equaivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __QKBO__
#define __QKBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Kernel/LASCA.hpp"

#include "Ordering.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/LaLpo.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

using namespace Lib;

template<class IfIter, class ElseIter>
static auto ifElseIter(bool cond, IfIter ifIter, ElseIter elseIter) 
{ return iterTraits(
         cond ? CoproductIter<Lib::ResultOf<IfIter>, Lib::ResultOf<ElseIter>>(ifIter())
              : CoproductIter<Lib::ResultOf<IfIter>, Lib::ResultOf<ElseIter>>(elseIter())); }


// TODO move to right place (LASCA.hpp ?)
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

class QKbo 
  : public Ordering
{
public:
  CLASS_NAME(QKbo);
  USE_ALLOCATOR(QKbo);

  QKbo(QKbo&& kbo) = default;
  QKbo& operator=(QKbo&& kbo) = default;
  explicit QKbo(KBO kbo);

  QKbo(Problem& prb, const Options& opts) 
    : QKbo(KBO(prb,opts, /* qkboPrecedence */ true)) {}

  virtual ~QKbo() {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final override;

  void show(ostream& out) const final override;

  Comparison compareFunctors(unsigned fun1, unsigned fun2) const override { ASSERTION_VIOLATION }

  void setState(std::shared_ptr<LascaState> s) { _shared = std::move(s); }

private:
  template<class NumTraits>
  WeightedMultiSet<SignedTerm> rmNum(std::tuple<IntegerConstantType, Perfect<Polynom<NumTraits>>> t) const
  {
    auto counts =  std::get<1>(t)->iterSummands()
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
          .template collect<Stack>();
    std::sort(counts.begin(), counts.end(), [](auto& l, auto& r) { return std::get<0>(l) < std::get<0>(r); });
    return WeightedMultiSet<SignedTerm>(std::get<0>(t), MultiSet<SignedTerm>::fromSortedStack(std::move(counts)));
  }

  std::tuple<IntegerConstantType, Perfect<Polynom<IntTraits>>> divNf(Perfect<Polynom<IntTraits>> t) const
  { return std::make_tuple(IntegerConstantType(1), t); }

  template<class NumTraits>
  std::tuple<IntegerConstantType, Perfect<Polynom<NumTraits>>> divNf(Perfect<Polynom<NumTraits>> t) const
  {
    auto l = t->iterSummands()
      .map([](auto s) { return s.numeral.denominator(); })
      .fold(IntegerConstantType(1), [&](auto acc, auto next) 
               { return IntegerConstantType::lcm(acc, next); });
    return std::make_tuple(l.abs(), typename NumTraits::ConstantType(l, IntegerConstantType(1)) * t);
  }

  auto asClosure() const 
  { return [this](auto const& l, auto const& r) { return this->compare(l, r); }; }

#ifdef VDEBUG
public:
#endif
  using SignedAtoms = WeightedMultiSet<SignedTerm>;

  template<class NumTraits>
  Option<SignedAtoms> signedAtoms(TermList t) const
  {
    auto norm = _shared->normalize(TypedTermList(t, NumTraits::sort())).template wrapPoly<NumTraits>();
    auto atoms = rmNum(divNf(norm));
    if (hasSubstitutionProperty(atoms)) {
      return Option<decltype(atoms)>(std::move(atoms));
    } else {
      return Option<decltype(atoms)>();
    }
  }

  template<class NumTraits>
  MultiSet<TermList> nfEquality(Literal* l) const
  {
    ASS(l->isEquality())
    using Num = typename NumTraits::ConstantType;
    auto norm = _shared->renormalize<NumTraits>(l).unwrap();
    return MultiSet<TermList> {
      NumTraits::sum(
          iterTraits(norm.term().iterSummands())
            .filter([](auto x) { return x.numeral >= Num(0);  })
            .map([](auto x) { return x.denormalize(); })),
      NumTraits::sum(iterTraits(norm.term().iterSummands())
          .filter([](auto x) { return x.numeral <= Num(0);  })
          .map([](auto x) { return (-x).denormalize(); }))
    };
  }


  static constexpr uint8_t POS_EQ_LEVEL = 0;
  static constexpr uint8_t NEG_EQ_LEVEL = 1;
  bool hasSubstitutionProperty(SignedAtoms const& l) const;

  using AtomsWithLvl = std::tuple<SignedAtoms, uint8_t>;

  template<class NumTraits>
  // the signs are not used here, but only there since we reuse code from signedAtoms and don't want to copy the datastructure.
  Option<AtomsWithLvl> atomsWithLvl(Literal* literal) const
  {
    auto mainIdx = literal->isEquality() && literal->termArg(0) == NumTraits::zero() ? 1 : 0;

    auto term = NumTraits::zero() == literal->termArg(1 - mainIdx) ? literal->termArg(mainIdx)
                                                                   : NumTraits::add(literal->termArg(0), NumTraits::minus(literal->termArg(1)));
    auto level = literal->isEquality() && literal->isPositive() ? POS_EQ_LEVEL : NEG_EQ_LEVEL;
    return signedAtoms<NumTraits>(term)
      .map([level](auto atoms) {
          return std::make_tuple(std::move(atoms), level);
      });
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
      auto multiset = MultiSet<SignedTerm>({ 
        // the sign is only a dummy here to match the type of atomsWithLvl<NumTraits>
          SignedTerm::zero(literal->termArg(0)), 
          SignedTerm::zero(literal->termArg(1)), 
        });
      return Option<AtomsWithLvl>(std::make_tuple(WeightedMultiSet<SignedTerm>(
              IntegerConstantType(1),
              std::move(multiset)), level));
    };
  } 

private:

  Result cmpNonAbstr(TermList, TermList) const;
  Option<TermList> abstr(TermList) const;

  std::shared_ptr<LascaState> _shared;
  KBO _kbo;
};

} // namespace Kernel

#endif // __QKBO__
