/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/Cancellation.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {


Cancellation::~Cancellation() {}


template<class Number>
struct CancelAddResult {
  Polynom<Number> lhs;
  Polynom<Number> rhs;
};

template<class Number>
CancelAddResult<Number> cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr) ;

template<class NumTraits>
Literal* cancelAdd(Literal* lit) {
  CALL("cancelAdd(Literal* lit)")
  ASS_EQ(lit->numTypeArguments(), 0) // <- we only have equality, or inequality literals, which are not polymorphic
  ASS_EQ(lit->numTermArguments(), 2)

  auto normL = PolyNf::normalize(TypedTermList((*lit)[0], SortHelper::getTermArgSort(lit, 0)));
  auto normR = PolyNf::normalize(TypedTermList((*lit)[1], SortHelper::getTermArgSort(lit, 1)));

  auto oldL = normL.template wrapPoly<NumTraits>();
  auto oldR = normR.template wrapPoly<NumTraits>();
  // TODO prevent copying here
  auto res = cancelAdd(oldL, oldR);

  res.lhs.integrity();
  res.rhs.integrity();

  if (res.lhs != oldL || res.rhs != oldR)  {
    TermList args[] = {res.lhs.denormalize(), res.rhs.denormalize()};
    return Literal::create(lit, args);
  } else  {
    return lit;
  }
}

Literal* tryCancel(Interpretation inter, Literal* lit) {
  CALL("tryCancel(Interpretation inter, Literal* lit)")
  switch(inter) {
    case Interpretation::EQUAL: {
        auto sort = SortHelper::getEqualityArgumentSort(lit);
        if (sort ==  IntTraits::sort()) return cancelAdd< IntTraits>(lit);
        if (sort ==  RatTraits::sort()) return cancelAdd< RatTraits>(lit);
        if (sort == RealTraits::sort()) return cancelAdd<RealTraits>(lit);
      }
      break;
#define INEQ_CASES(NumTraits)                                                                                 \
    case NumTraits::leqI:                                                                                     \
    case NumTraits::geqI:                                                                                     \
    case NumTraits::greaterI:                                                                                 \
    case NumTraits::lessI:                                                                                    \
      return cancelAdd<NumTraits>(lit); 

    INEQ_CASES( IntTraits)
    INEQ_CASES( RatTraits)
    INEQ_CASES(RealTraits)
#undef INEQ_CASES
    default:;
  }
  return lit;
}

Cancellation::Cancellation(Ordering& ordering) : SimplifyingGeneratingLiteralSimplification(InferenceRule::CANCELLATION, ordering) {}

Cancellation::Result Cancellation::simplifyLiteral(Literal* litIn) 
{
  CALL("Cancellation::simplifyLiteral(Literal*)")

  auto pred = litIn->functor();
  return Result::literal(
              theory->isInterpretedPredicate(pred) 
                ? tryCancel(theory->interpretPredicate(pred), litIn)
                : litIn);
}

template<class Number>
CancelAddResult<Number> cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr) 
{
  CALL("Polynom::cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr)")
  DEBUG("in:  ", oldl, " <> ", oldr)

  using Numeral = typename Number::ConstantType;
  using Monom        = Monom       <Number>;
  using MonomFactors = MonomFactors<Number>;
  auto itl = oldl.iterSummands();
  auto itr = oldr.iterSummands();

  auto safeMinus = [](Numeral l, Numeral r) 
  { 
    try {
      return Option<Numeral>(l - r);
    } catch (MachineArithmeticException&)
    {
      return Option<Numeral>();
    }
  };

  auto cmpPrecedence = [](Option<Numeral> lOpt, Numeral r) 
  { 
    if (lOpt.isNone()) return false;
    auto l = lOpt.unwrap();
    return Numeral::comparePrecedence(l,r) == Comparison::LESS;
  };


  Stack<Monom> newl;
  Stack<Monom> newr;
  auto pushRes = [&](auto& res, auto t) { res.push(t); };

  auto _l = itl.tryNext();
  auto _r = itr.tryNext();
  while (_l.isSome() && _r.isSome()) {
    auto const &l = _l.unwrap();
    auto const &r = _r.unwrap();
    if (l.factors == r.factors) {
      auto& m = l.factors;

      auto lMinusR = safeMinus(l.numeral, r.numeral);
      auto rMinusL = safeMinus(r.numeral, l.numeral);
      auto pushDiffLeft  = [&]() { pushRes(newl, Monom(lMinusR.unwrap(), MonomFactors(m))); };
      auto pushDiffRight = [&]() { pushRes(newr, Monom(rMinusL.unwrap(), MonomFactors(m))); };
      auto pushSmaller = [&] () {
        if (cmpPrecedence(rMinusL, lMinusR.unwrap())) {
          pushDiffRight();
        } else {
          pushDiffLeft();
        }
      };



      if (l.numeral == r.numeral) {
         // 10 x + ... ~~  10 x + ... ==> ... ~~ ... 
         // we remove the term
      } else if (cmpPrecedence(lMinusR, l.numeral) 
              && cmpPrecedence(rMinusL, r.numeral)) {

        pushSmaller();
      } else if (cmpPrecedence(lMinusR, l.numeral) ) {
        // 10 x + ... ~~  8 x + ... ==> 2 x + ... ~~ ... 
        // ^^ l.numeral   ^ r.numeral   ^ lMinusR
        pushDiffLeft();

      } else if (cmpPrecedence(rMinusL, r.numeral)) {
        //   7 x + ... ~~  8 x + ... ==> ... ~~ 1 x + ... 
        //   ^ l.numeral   ^ r.numeral          ^ rMinusL
        pushDiffRight();
      } else {

        if (lMinusR.isSome() && rMinusL.isSome()){
          pushSmaller();
        } else if (lMinusR.isSome()) {
          pushDiffLeft();
        } else if (rMinusL.isSome()) {
          pushDiffRight();
        } else {
          ASS_EQ(m, l.factors);
          ASS_EQ(m, r.factors);
          pushRes(newl, l);
          pushRes(newr, r);
        }
      }
      _l = itl.tryNext();
      _r = itr.tryNext();
    } else if (l.factors < r.factors) {
      pushRes(newl, l);
      _l = itl.tryNext();
    } else {
      ASS(r.factors < l.factors)
      pushRes(newr, r);
      _r = itr.tryNext();
    }
  } 

  while (_l.isSome()) {
    pushRes(newl, _l.unwrap());
    _l = itl.tryNext();
  }
  while (_r.isSome()) {
    pushRes(newr, _r.unwrap());
    _r = itr.tryNext();
  }
  auto outl = Polynom<Number>(std::move(newl));
  auto outr = Polynom<Number>(std::move(newr));
  DEBUG("out: ", outl, " <> ", outr)
  return CancelAddResult<Number> { 
    .lhs = std::move(outl), 
    .rhs = std::move(outr), 
  };
}



} // namespace Inferences
