/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "IRC.hpp"
#include "Kernel/LaLpo.hpp"

namespace Kernel {
using Inferences::PolynomialEvaluation;

bool isInequality(IrcPredicate const& self) 
{
  switch(self) {
    case IrcPredicate::EQ: 
    case IrcPredicate::NEQ: return false;
    case IrcPredicate::GREATER: 
    case IrcPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}

std::ostream& operator<<(std::ostream& out, IrcPredicate const& self)
{ 
  switch(self) {
    case IrcPredicate::EQ: return out << "==";
    case IrcPredicate::NEQ: return out << "!=";
    case IrcPredicate::GREATER: return out << ">";
    case IrcPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
}


Literal* InequalityNormalizer::normalizeLiteral(Literal* lit) const 
{
  return           normalizeIrc< IntTraits>(lit).map([](auto l) { return l.value.denormalize(); })
  || [&](){ return normalizeIrc< RatTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
  || [&](){ return normalizeIrc<RealTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
  || lit;
}

bool InequalityNormalizer::isNormalized(Clause* cl)  const
{ 
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    if(lit != normalizeLiteral(lit)) {
      return false;
    }
  }
  return true;
}

#if VDEBUG
shared_ptr<IrcState> testIrcState(Options::UnificationWithAbstraction uwa) {
  auto& ord = *new LaLpo(Precedence::random());
  return shared_ptr<IrcState>(new IrcState {
      .normalizer = InequalityNormalizer(),
      .ordering = &ord,
      .uwa = uwa,
  });
}
#endif

Option<MaybeOverflow<AnyIrcLiteral>> InequalityNormalizer::normalize(Literal* lit) const
{
  using Out = AnyIrcLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto overflown) { return overflown.map([](auto x) { return Out(x); }); });
  };
  return             wrapCoproduct(normalizeIrc< IntTraits>(lit))
    || [&](){ return wrapCoproduct(normalizeIrc< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(normalizeIrc<RealTraits>(lit)); } 
    || Option<MaybeOverflow<Out>>();
}

Stack<Literal*> IrcState::maxLiterals(Clause* cl, bool strictlyMax)
{
  return maxElements([&](auto i) { return (*cl)[i]; }, 
                     cl->size(),
                     [&](auto l, auto r) { return ordering->compare(l, r); },
                     strictlyMax);
  // auto size    = 
  // auto getElem = 
  // auto cmp     = [&](auto l, auto r) { return ordering->compare(l, r); }
  //
  // Stack<decltype(getElem(0))> max(size); // TODO not sure whether this size allocation brings an advantage
  // // auto monoms = lit.term().iterSummands().template collect<Stack>();
  // for (unsigned i = 0; i < size; i++) {
  //   auto isMax = true;
  //   for (unsigned j = 0; j < size; j++) {
  //     auto cmp = cmp(getElem(i), getElem(j));
  //     if (cmp == Ordering::LESS) {
  //       isMax = false;
  //       break;
  //     } else if (cmp == Ordering::EQUAL || cmp == Ordering::INCOMPARABLE || Ordering::GREATER) {
  //       /* ok */
  //     } else {
  //       ASSERTION_VIOLATION_REP(cmp)
  //     }
  //   }
  //   if (isMax)  // TODO we don't wanna skip varibles in the future
  //     max.push(getElem(i));
  // }
  // return max;
}


Option<AnyIrcLiteral> IrcState::normalize(Literal* lit)
{
  return this->normalizer.normalize(lit)
    .andThen([](auto res) {
        // TODO overflow statistic
        return res.overflowOccurred 
          ? Option<AnyIrcLiteral>()
          : Option<AnyIrcLiteral>(res.value);
        });
}


Option<AnyInequalityLiteral> IrcState::normalizeIneq(Literal* lit)
{
  return normalize(lit)
    .andThen([](auto res) {
      return res.apply([](auto lit) { 
          return inequalityLiteral(lit).map([](auto x) { return AnyInequalityLiteral(x); }); 
      });
    });
}

PolyNf IrcState::normalize(TypedTermList term) 
{ 
  auto norm = PolyNf::normalize(term);
  auto out = this->normalizer.evaluator().evaluate(norm); 
  ASS(!out.overflowOccurred)
  return out.value || norm;
}

Option<UwaResult> IrcState::unify(TermList lhs, TermList rhs) const 
{
  UwaResult out;
  Kernel::UWAMismatchHandler hndlr(uwa, out.cnst);
  if (out.sigma.unify(lhs, /* var bank: */ 0, 
                      rhs, /* var bank: */ 0, &hndlr)) {
    return Option<UwaResult>(std::move(out));
  } else {
    return Option<UwaResult>();
  }
}

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect)
{ return toCorrect.intDivide(gcd); }


IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r)
{ return IntegerConstantType::gcd(l, r); }

Ordering::Result compare(IrcPredicate l, IrcPredicate r) 
{
       if (l < r)  return Ordering::Result::LESS;
  else if (l > r)  return Ordering::Result::GREATER;
  else if (l == r) return Ordering::Result::EQUAL;
  else ASSERTION_VIOLATION
}

} // namespace Kernel

