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

#define DEBUG(...) //DBG(__VA_ARGS__)

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
  ASS_EQ(lit->numTypeArguments(), 0) // <- we only have equality, or inequality literals, which are not polymorphic
  ASS_EQ(lit->numTermArguments(), 2)
  auto normL = PolyNf::normalize(TypedTermList((*lit)[0], SortHelper::getTermArgSort(lit, 0)));
  auto normR = PolyNf::normalize(TypedTermList((*lit)[1], SortHelper::getTermArgSort(lit, 1)));

  auto oldL = normL.template wrapPoly<NumTraits>();
  auto oldR = normR.template wrapPoly<NumTraits>();
  auto res = cancelAdd(*oldL, *oldR);

  res.lhs.integrity();
  res.rhs.integrity();

  auto newL = perfect(std::move(res.lhs));
  auto newR = perfect(std::move(res.rhs));

  if (newL != oldL || newR != oldR)  {
    TermList args[] = {
      newL->denormalize(),
      newR->denormalize(),
    };
    return Literal::create(lit, args);
  } else  {
    return lit;
  }
}

Literal* tryCancel(Interpretation inter, Literal* lit) {
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
  auto pred = litIn->functor();
  return Result::literal(
              theory->isInterpretedPredicate(pred) 
                ? tryCancel(theory->interpretPredicate(pred), litIn)
                : litIn);
}

template<class Number>
CancelAddResult<Number> cancelAdd(Polynom<Number> const& oldl, Polynom<Number> const& oldr) 
{
  DEBUG("in:  ", oldl, " <> ", oldr)

  using Numeral = typename Number::ConstantType;
  using Monom        = Monom       <Number>;
  using NumeralVec   = Stack<Monom>;
  unsigned itl = 0;
  unsigned itr = 0;
  auto endl = oldl.nSummands();
  auto endr = oldr.nSummands();

  auto cmpPrecedence = [](Numeral l, Numeral r) 
  { return Numeral::comparePrecedence(l,r) == Comparison::LESS; };

  NumeralVec newl;
  NumeralVec newr;
  while(itl != endl && itr !=  endr) {
    auto l = oldl.summandAt(itl);
    auto r = oldr.summandAt(itr);
    if (l.factors == r.factors) {
      auto& m = l.factors;

      auto lMinusR = l.numeral - r.numeral;
      auto rMinusL = r.numeral - l.numeral;
      auto pushDiffLeft  = [&]() { newl.push(Monom(lMinusR, m)); };
      auto pushDiffRight = [&]() { newr.push(Monom(rMinusL, m)); };
      auto pushSmaller = [&] () {
        if (cmpPrecedence(rMinusL, lMinusR)) {
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
        pushSmaller();

      }
      itl++;
      itr++;
    } else if (l.factors < r.factors) {
      newl.push(l);
      itl++;
    } else {
      ASS(r.factors < l.factors)
      newr.push(r);
      itr++;
    }
  }
  for(; itl != endl; itl++) {
    newl.push(oldl.summandAt(itl));
  }
  for(; itr != endr; itr++) {
    newr.push(oldr.summandAt(itr));
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
