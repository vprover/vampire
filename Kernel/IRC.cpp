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

#define DEBUG(...) // DBG(__VA_ARGS__)
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


// Literal* InequalityNormalizer::renormalizeLiteral(Literal* lit) const 
// {
//   return           renormalizeIrc< IntTraits>(lit).map([](auto l) { return l.value.denormalize(); })
//   || [&](){ return renormalizeIrc< RatTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
//   || [&](){ return renormalizeIrc<RealTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
//   || lit;
// }


Literal* InequalityNormalizer::normalizeUninterpreted(Literal* lit) const 
{
  CALL("InequalityNormalizer::normalizeUninterpreted(Literal* lit) const")
  Stack<TermList> args(lit->arity());
  for (unsigned i = 0; i < lit->arity(); i++) {
    auto orig = *lit->nthArgument(i);
    if (orig.isVar()) {
      args.push(orig);
    } else {
      auto eval = evaluator()
        .evaluate(PolyNf::normalize(TypedTermList(orig.term())))
        .value.map([](auto t) { return t.denormalize(); }) 
        || orig;  // <- nothing was done during evaluation
      args.push(eval);;
    }
  }
  auto out = Literal::create(lit, args.begin());
  DEBUG(*lit, " ==> ", *out)
  return out;
}

Stack<Literal*> InequalityNormalizer::normalizeLiteral(Literal* lit) const 
{
  auto out = tryNumTraits([&](auto numTraits)  -> Option<Stack<Literal*>> { 
      return normalizeIrc<decltype(numTraits)>(lit)
              .map([](auto lits) { 
                  return iterTraits(lits.value.iterFifo())
                        .map([](auto lit) { return lit.denormalize(); })
                        .template collect<Stack>(); 
                }); 
    }) || [&]() { return Stack<Literal*>{normalizeUninterpreted(lit)}; };
  DEBUG(*lit, " ==> ", out)
  return out;
}

bool InequalityNormalizer::isNormalized(Clause* cl)  const
{ 
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    auto norm = normalizeLiteral(lit);
    if(norm.size() != 1 || lit != norm[0]) {
      return false;
    }
  }
  return true;
}

#if VDEBUG
shared_ptr<IrcState> testIrcState(Options::UnificationWithAbstraction uwa, bool strongNormalization, Ordering* ordering) {

  auto& ord = ordering == nullptr ? *new LaLpo(Precedence::random()) : *ordering;
  return shared_ptr<IrcState>(new IrcState {
      .normalizer = InequalityNormalizer(strongNormalization),
      .ordering = &ord,
      .uwa = uwa,
  });
}
#endif

Option<MaybeOverflow<AnyIrcLiteral>> InequalityNormalizer::renormalize(Literal* lit) const
{
  using Out = AnyIrcLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto overflown) { return overflown.map([](auto x) { return Out(x); }); });
  };
  return             wrapCoproduct(renormalizeIrc< IntTraits>(lit))
    || [&](){ return wrapCoproduct(renormalizeIrc< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(renormalizeIrc<RealTraits>(lit)); } 
    || Option<MaybeOverflow<Out>>();
}

Stack<Literal*> IrcState::maxLiterals(Clause* cl, bool strictlyMax)
{
  return maxElements([&](auto i) { return (*cl)[i]; }, 
                     cl->size(),
                     [&](auto l, auto r) { return ordering->compare(l, r); },
                     strictlyMax);
}


Stack<Literal*> IrcState::maxLiterals(Stack<Literal*> cl, bool strictlyMax)
{
  return maxElements([&](auto i) { return cl[i]; }, 
                     cl.size(),
                     [&](auto l, auto r) { return ordering->compare(l, r); },
                     strictlyMax);
}


Option<AnyIrcLiteral> IrcState::renormalize(Literal* lit)
{
  return this->normalizer.renormalize(lit)
    .andThen([](auto res) {
        // TODO overflow statistic
        return res.overflowOccurred 
          ? Option<AnyIrcLiteral>()
          : Option<AnyIrcLiteral>(res.value);
        });
}


Option<AnyInequalityLiteral> IrcState::renormalizeIneq(Literal* lit)
{
  return renormalize(lit)
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

