/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "LASCA.hpp"
#include "Lib/Stack.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/QKbo.hpp"
// #include "Kernel/LaLpo.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
namespace Kernel {
using Inferences::PolynomialEvaluation;

bool isInequality(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: return false;
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}

std::ostream& operator<<(std::ostream& out, LascaPredicate const& self)
{ 
  switch(self) {
    case LascaPredicate::EQ: return out << "==";
    case LascaPredicate::NEQ: return out << "!=";
    case LascaPredicate::GREATER: return out << ">";
    case LascaPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
}


// Literal* InequalityNormalizer::renormalizeLiteral(Literal* lit) const 
// {
//   return           renormalizeLasca< IntTraits>(lit).map([](auto l) { return l.value.denormalize(); })
//   || [&](){ return renormalizeLasca< RatTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
//   || [&](){ return renormalizeLasca<RealTraits>(lit).map([](auto l) { return l.value.denormalize(); }); }
//   || lit;
// }


Literal* InequalityNormalizer::normalizeUninterpreted(Literal* lit) const 
{
  CALL("InequalityNormalizer::normalizeUninterpreted(Literal* lit) const")
  Stack<TermList> args(lit->arity());
  args.loadFromIterator(typeArgIter(lit));
  for (auto orig : termArgIter(lit)) {
    if (orig.isVar()) {
      args.push(orig);
    } else {
      auto norm = PolyNf::normalize(TypedTermList(orig.term()));
      auto eval = evaluator()
        .evaluate(norm)
        .value.map([](auto t) { return t.denormalize(); }) 
        || norm.denormalize();  // <- nothing was done during evaluation
      args.push(eval);
    }
  }
  auto out = Literal::create(lit, args.begin());
  DEBUG(*lit, " ==> ", *out)
  return out;
}

Stack<Literal*> InequalityNormalizer::normalizeLiteral(Literal* lit) const 
{
  auto out = tryNumTraits([&](auto numTraits)  -> Option<Stack<Literal*>> { 
      return normalizeLasca<decltype(numTraits)>(lit)
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
shared_ptr<LascaState> testLascaState(Options::UnificationWithAbstraction uwa, bool strongNormalization, Ordering* ordering) {

  auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/*rand*/ false, /*qkbo*/ true)) : nullptr;
  auto& ord = ordering == nullptr ? *qkbo : *ordering;
  auto state = LascaState::create(InequalityNormalizer(strongNormalization), &ord, uwa);
  if (qkbo)
        qkbo->setState(state);
  return state;
}
#endif

std::ostream& operator<<(std::ostream& out, SelectedSummand const& self)
{ 
  self.numeral().apply([&](auto n) -> void { out << n; });
  out << " " << self.monom();
  self.numTraits()
    .apply([&](auto numTraits) {
      for (auto s : self.contextTerms<decltype(numTraits)>()) {
        out << " + " << s;
      }
    });
  out << " " << self.symbol() << " 0";
  for (auto l : self.contextLiterals()) {
    out << " \\/ " << *l;
  }
  return out; 
}

Option<MaybeOverflow<AnyLascaLiteral>> InequalityNormalizer::renormalize(Literal* lit) const
{
  using Out = AnyLascaLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto overflown) { return overflown.map([](auto x) { return Out(x); }); });
  };
  return             wrapCoproduct(renormalizeLasca< IntTraits>(lit))
    || [&](){ return wrapCoproduct(renormalizeLasca< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(renormalizeLasca<RealTraits>(lit)); } 
    || Option<MaybeOverflow<Out>>();
}

// Stack<std::pair<Literal*, unsigned>> LascaState::selectedLiteralsWithIdx(Clause* cl, bool strictlyMax)
// {
//   return iterTraits(getRangeIterator((unsigned)0, cl->numSelected()))
//     .map([=](auto i) 
//         { return make_pair((*cl)[i], i); })
//     .template collect<Stack>();
// }
//
//
// Stack<Literal*> LascaState::selectedLiterals(Clause* cl, bool strictlyMax)
// {
//   // TODO use strictly max
//   return iterTraits(cl->getSelectedLiteralIterator()).template collect<Stack>();
// }
//
//
// Stack<std::pair<Literal*, unsigned>> LascaState::maxLiteralsWithIdx(Clause* cl, bool strictlyMax)
// {
//   return maxElements([&](unsigned i) { return make_pair((*cl)[i], i); }, 
//                      cl->size(),
//                      [&](auto l, auto r) { return ordering->compare(l.first, r.first); },
//                      strictlyMax);
// }
//
//
// Stack<Literal*> LascaState::maxLiterals(Clause* cl, bool strictlyMax)
// {
//   return maxElements([&](auto i) { return (*cl)[i]; }, 
//                      cl->size(),
//                      [&](auto l, auto r) { return ordering->compare(l, r); },
//                      strictlyMax);
// }
//
//
// Stack<Literal*> LascaState::maxLiterals(Stack<Literal*> cl, bool strictlyMax)
// {
//   return maxElements([&](auto i) { return cl[i]; }, 
//                      cl.size(),
//                      [&](auto l, auto r) { return ordering->compare(l, r); },
//                      strictlyMax);
// }


Option<AnyLascaLiteral> LascaState::renormalize(Literal* lit)
{
  return this->normalizer.renormalize(lit)
    .andThen([](auto res) {
        // TODO overflow statistic
        return res.overflowOccurred 
          ? Option<AnyLascaLiteral>()
          : Option<AnyLascaLiteral>(res.value);
        });
}


Option<AnyInequalityLiteral> LascaState::renormalizeIneq(Literal* lit)
{
  return renormalize(lit)
    .andThen([](auto res) {
      return res.apply([](auto lit) { 
          return inequalityLiteral(lit).map([](auto x) { return AnyInequalityLiteral(x); }); 
      });
    });
}

PolyNf LascaState::normalize(TypedTermList term) 
{ 
  TIME_TRACE("lasca normalize term")
  auto norm = PolyNf::normalize(term);
  auto out = this->normalizer.evaluator().evaluate(norm); 
  if (out.overflowOccurred)  {
    WARN("failed to normalize: ", out.value)
    throw MachineArithmeticException("overflow while normalizing irc term");
  }
  return out.value || norm;
}

Option<UwaResult> LascaState::unify(TermList lhs, TermList rhs) const 
{
  RobSubstitution sigma;
  Stack<UnificationConstraint> cnst;
  Kernel::UWAMismatchHandler hndlr(uwa, cnst);
  if (sigma.unify(lhs, /* var bank: */ 0, 
                  rhs, /* var bank: */ 0, &hndlr)) {
    return Option<UwaResult>(UwaResult(std::move(sigma), std::move(cnst)));
  } else {
    return Option<UwaResult>();
  }
}

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect)
{ return toCorrect.intDivide(gcd); }


IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r)
{ return IntegerConstantType::gcd(l, r); }

Ordering::Result compare(LascaPredicate l, LascaPredicate r) 
{
       if (l < r)  return Ordering::Result::LESS;
  else if (l > r)  return Ordering::Result::GREATER;
  else if (l == r) return Ordering::Result::EQUAL;
  else ASSERTION_VIOLATION
}

SelectedLiteral::SelectedLiteral(Clause* clause, unsigned litIdx, LascaState& shared)
  : cl(clause)
  , litIdx(litIdx)
  , interpreted(shared.renormalize(literal()))
{}

std::shared_ptr<LascaState> LascaState::globalState = nullptr;

} // namespace Kernel

