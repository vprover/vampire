/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InequalityResolutionCalculus.hpp"

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

} // namespace Kernel

