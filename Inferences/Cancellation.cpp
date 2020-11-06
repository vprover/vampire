#include "Inferences/Cancellation.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

namespace Inferences {


Cancellation::~Cancellation() {}

template<class NumTraits>
Literal* doCancellation(Literal* lit) {
  auto normL = PolyNf::normalize(TypedTermList((*lit)[0], SortHelper::getArgSort(lit, 0)));
  auto normR = PolyNf::normalize(TypedTermList((*lit)[1], SortHelper::getArgSort(lit, 1)));

  auto oldL = normL.template wrapPoly<NumTraits>();
  auto oldR = normR.template wrapPoly<NumTraits>();
  auto res = Polynom<NumTraits>::cancelAdd(*oldL, *oldR);
  auto newL = perfect(std::move(res.lhs));
  auto newR = perfect(std::move(res.rhs));
  if (newL != oldL || newR != oldR)  {
    TermList args[] = {
      res.lhs.denormalize(),
      res.rhs.denormalize(),
    };
    return Literal::create(lit, args);
  } else  {
    return lit;
  }
}

Literal* tryCancel(Interpretation inter, Literal* lit) {
  switch(inter) {
    case Interpretation::EQUAL:
      switch (SortHelper::getEqualityArgumentSort(lit)) {
        case  IntTraits::sort: return doCancellation< IntTraits>(lit);
        case  RatTraits::sort: return doCancellation< RatTraits>(lit);
        case RealTraits::sort: return doCancellation<RealTraits>(lit);
        default:;
      }
      break;
#define INEQ_CASES(NumTraits)                                                                                 \
    case NumTraits::leqI:                                                                                     \
    case NumTraits::geqI:                                                                                     \
    case NumTraits::greaterI:                                                                                 \
    case NumTraits::lessI:                                                                                    \
      return doCancellation<NumTraits>(lit); 

    INEQ_CASES( IntTraits)
    INEQ_CASES( RatTraits)
    INEQ_CASES(RealTraits)
#undef INEQ_CASES
    default:;
  }
  return lit;
}

// TODO make Canellation its own InferenceRule
Cancellation::Cancellation(Ordering& ordering) : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering) {}

Cancellation::Result Cancellation::simplifyLiteral(Literal* litIn) 
{
  CALL("Cancellation::simplifyLiteral(Literal*)")

  auto pred = litIn->functor();
  return Result::literal(
              theory->isInterpretedPredicate(pred) 
                ? tryCancel(theory->interpretPredicate(pred), litIn)
                : litIn);
}


} // namespace Inferences
