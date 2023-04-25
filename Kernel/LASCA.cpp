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
#include "Kernel/Inference.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Stack.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/QKbo.hpp"
#include "Kernel/Problem.hpp"
// #include "Kernel/LaLpo.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
namespace Kernel {
using Inferences::PolynomialEvaluation;

bool isInequality(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: 
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: return false;
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}

bool isIsInt(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: return true;
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: 
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return false;
  }
  ASSERTION_VIOLATION
}

std::ostream& operator<<(std::ostream& out, LascaPredicate const& self)
{ 
  switch(self) {
    case LascaPredicate::IS_INT_POS: return out << "isInt";
    case LascaPredicate::IS_INT_NEG: return out << "~isInt";
    case LascaPredicate::EQ: return out << "==";
    case LascaPredicate::NEQ: return out << "!=";
    case LascaPredicate::GREATER: return out << ">";
    case LascaPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
}


bool LascaState::hasSubstitutionProperty(SignedAtoms const& l)
{

  auto maybeEquiv = [this](TermList l, TermList r) -> bool 
  {
    ASS_NEQ(l, r)

    if (l.ground() && r.ground()) {
      return this->equivalent(l.term(), r.term());

    } else if (this->unify(l, r).isSome()) {
      return true;

    } else {
      return false;
    }
  };

  Stack<TermList> pos;
  Stack<TermList> neg;
  for (auto const& t_ : l.elems.iter()) {
    auto const& sign = std::get<0>(t_).sign;
    auto const& term = std::get<0>(t_).term;

    if (term.isVar() && sign != Sign::Zero) {
      if (concatIters(pos.iterFifo(), neg.iterFifo()).any([&](auto s) { return maybeEquiv(s, term); })) {
        return false;
      }
      pos.push(term);
      neg.push(term);
    } else if (sign != Sign::Zero) {

      auto& same  = sign == Sign::Pos ? pos : neg;
      auto& other = sign == Sign::Pos ? neg : pos;

      if (iterTraits(other.iterFifo())
        .any([&](auto& s) { return maybeEquiv(s, term); })) 
      {
          return false;
      }
      same.push(term);
    }
  }
  return true;
}


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

Recycled<Stack<Literal*>> InequalityNormalizer::normalizeLiteral(Literal* lit) const 
{
  Recycled<Stack<Literal*>> out;
  auto num = forAnyNumTraits([&](auto numTraits) { 
      auto norm = normalizeLasca<decltype(numTraits)>(lit);
      if (norm.isSome()) {
        out->loadFromIterator(
          arrayIter(norm->value)
            .map([](auto lit) { return lit.denormalize(); }));
        return true;
      } else {
        return false;
      }
    }); 
  if (!num) {
    out->push(normalizeUninterpreted(lit));
  }
  DEBUG(*lit, " ==> ", out)
  return out;
}

bool InequalityNormalizer::isNormalized(Clause* cl)  const
{ 
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    auto norm = normalizeLiteral(lit);
    if(norm->size() != 1 || lit != (*norm)[0]) {
      return false;
    }
  }
  return true;
}

#if VDEBUG
shared_ptr<LascaState> testLascaState(Options::UnificationWithAbstraction uwa, bool strongNormalization, Ordering* ordering, bool uwaFixedPointIteration) {

  auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/*rand*/ false, /*qkbo*/ true)) : nullptr;
  auto& ord = ordering == nullptr ? *qkbo : *ordering;
  auto state = LascaState::create(InequalityNormalizer(strongNormalization), &ord, uwa, uwaFixedPointIteration);
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

Option<AbstractingUnifier> LascaState::unify(TermList lhs, TermList rhs) const 
{ return AbstractingUnifier::unify(lhs, 0, rhs, 0, uwaMode(), uwaFixedPointIteration); }

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

void LascaState::realization(Problem& p)
{
  auto trans = tranlateSignature();
  auto& fs  = trans.first;
  auto& ps  = trans.second;
  auto translateTerm = [&](TermList t) -> TermList { 
    return t; 
  };
  auto translateLit = [&](Literal* lit) -> Literal* {
    return Literal::createFromIter(
        lit->polarity(),
        ps[lit->functor()], 
        anyArgIter(lit).map([&](auto arg) { return translateTerm(arg); }));
  };
  p.mapUnits([&](auto c_) {
      Recycled<Stack<Unit*>> out;
      ASS(c_->isClause());
      auto c =  static_cast<Clause*>(c_);
      Recycled<Stack<Literal*>> clOut;
      
      for (auto l : iterTraits(c->iterLits())) {
        
        auto itp = normalizer.normalizeLasca<IntTraits>(l);
        if (itp) {
          for (auto nl : itp->value) {
            clOut->push(RealTraits::isInt(false, nl.term().denormalize()));
          }
        }
        clOut->push(translateLit(l));
      }

      out->push(Clause::fromStack(*clOut, 
          Inference(FormulaTransformation(InferenceRule::ALASCAI_REALIZATION, c))));

      return out;
  });

  // for (auto p : range(0, env.signature->predicates())) {
  //   auto sym = env.signature->getPredicate(p);
  //   if (hasIntArgs(sym->predType())) {
  //   }
  //
  // }
  ASSERTION_VIOLATION_REP("TODO")
}

pair<Stack<unsigned>, Stack<unsigned>> LascaState::tranlateSignature()
{
  Stack<unsigned> fs;

  auto reals = RealTraits::sort();
  auto ints  = IntTraits::sort();

  auto iterArgs = [&](OperatorType* o)  
    { return range(0, o->arity())
               .map([&](auto i) { return o->arg(i); }); };


  auto mappedArgs = [&](OperatorType* o)  { 
      Recycled<Stack<TermList>> out;
      out->loadFromIterator(iterArgs(o)
          .map([&](auto a) {  return a == ints ? reals : a; }));
      return out;
    };

  auto hasIntArgs = [&](OperatorType* o)  
    { return iterArgs(o).any([&](auto a) { return a == ints; }); };

  for (auto f : range(0, env.signature->functions())) {
    ASS_REP(theory->isInterpretedFunction(f), "TODO")
    auto sym = env.signature->getFunction(f);
    auto op = sym->fnType();
    if (hasIntArgs(op) || op->result() == ints) {
      Recycled<Stack<TermList>> args = mappedArgs(op);
      auto res = op->result() == ints ? reals : op->result();
      
      fs.push(
            env.signature->addFreshFunction(
              OperatorType::getFunctionType(*args, res), 
              sym->name().c_str()));
    } else {
      fs.push(f);
    }
  }

  Stack<unsigned> ps;
  for (auto p : range(0, env.signature->predicates())) {
    ASS_REP(theory->isInterpretedPredicate(p), "TODO")
    auto sym = env.signature->getPredicate(p);
    auto op = sym->predType();
    if (hasIntArgs(op)) {
      Recycled<Stack<TermList>> args = mappedArgs(op);
      ps.push(
            env.signature->addFreshPredicate(
              OperatorType::getPredicateType(*args),
              sym->name().c_str()));
    } else {
      ps.push(p);
    }
  }
  return make_pair(std::move(fs), std::move(ps));
}

} // namespace Kernel

