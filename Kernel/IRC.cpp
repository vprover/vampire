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
      DBG(cl->toString())
      DBG(*lit, " != ", *normalizeLiteral(lit))
      return false;
    }
  }
  return true;
}

#if VDEBUG
shared_ptr<IrcState> testIrcState(Options::UnificationWithAbstraction uwa) {
  auto& ord = *new LaKbo(Kernel::KBO::testKBO());
  return shared_ptr<IrcState>(new IrcState {
      .normalizer = InequalityNormalizer(ord),
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

} // namespace Kernel

