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
#include "Debug/Assertion.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Stack.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/QKbo.hpp"
#include "Kernel/Problem.hpp"
// #include "Kernel/LaLpo.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
namespace Kernel {
using Inferences::PolynomialEvaluation;

// number type to which integers are being translated to
using R = RealTraits;

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


bool isEquality(LascaPredicate const& self) 
{
  switch(self) {
    case LascaPredicate::IS_INT_POS: 
    case LascaPredicate::IS_INT_NEG: 
    case LascaPredicate::GREATER: 
    case LascaPredicate::GREATER_EQ: return false;
    case LascaPredicate::EQ: 
    case LascaPredicate::NEQ: return true;
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

Option<std::function<TermList(TermList*)>> translateInterpretedFunction(unsigned f) {
  auto fn = [](auto x) { return some(std::function<TermList(TermList*)>(std::move(x))); };

  auto sym = env.signature->getFunction(f);
  if(sym->integerConstant()) {
    return fn([sym](auto x) { return R::constantTl(typename R::ConstantType(sym->integerValue(), IntegerConstantType(1))); });
  }

  if(!theory->isInterpretedFunction(f))
    return {};


  auto remainder = [](auto quotient)
  { return [quotient](TermList* ts) { return R::add(ts[0], R::minus(R::mul(ts[1], quotient(ts)))); }; };

  auto quotientF = [](TermList* ts) { return R::toInt(R::div(ts[0], ts[1])); };
  auto quotientE = [=](TermList* ts) { 
    return TermList(Term::createITE(new AtomicFormula(R::greater(true, ts[1], R::zero())),
          quotientF(ts),
          R::minus(R::toInt(R::minus(R::div(ts[0], ts[1])))),
          R::sort()));
  };

  switch(theory->interpretFunction(f)) {
    case Interpretation::EQUAL: 

    case Interpretation::INT_IS_INT: 
    case Interpretation::INT_IS_RAT: 
    case Interpretation::INT_IS_REAL: 
    case Interpretation::INT_GREATER: 
    case Interpretation::INT_GREATER_EQUAL: 
    case Interpretation::INT_LESS: 
    case Interpretation::INT_LESS_EQUAL: 
    case Interpretation::INT_DIVIDES: 
    case Interpretation::RAT_IS_INT:
    case Interpretation::RAT_IS_RAT:
    case Interpretation::RAT_IS_REAL:
    case Interpretation::RAT_GREATER:
    case Interpretation::RAT_GREATER_EQUAL:
    case Interpretation::RAT_LESS:
    case Interpretation::RAT_LESS_EQUAL:
    case Interpretation::REAL_IS_INT:
    case Interpretation::REAL_IS_RAT:
    case Interpretation::REAL_IS_REAL:
    case Interpretation::REAL_GREATER:
    case Interpretation::REAL_GREATER_EQUAL:
    case Interpretation::REAL_LESS:
    case Interpretation::REAL_LESS_EQUAL:
      ASSERTION_VIOLATION_REP("Not a function interpretation")

      //numeric functions

    case Interpretation::INT_SUCCESSOR:   return fn([](TermList* ts) { return R::add(ts[0], R::one()); });
    case Interpretation::INT_UNARY_MINUS: return fn([](TermList* ts) { return R::minus(ts[0]); });
    case Interpretation::INT_PLUS:        return fn([](TermList* ts) { return R::add(ts[0], ts[1]); });
    case Interpretation::INT_MINUS:       return fn([](TermList* ts) { return R::add(ts[0], R::minus(ts[1])); });
    case Interpretation::INT_MULTIPLY:    return fn([](TermList* ts) { return R::mul(ts[0], ts[1]); });

    case Interpretation::INT_CEILING:
    case Interpretation::INT_TRUNCATE:
    case Interpretation::INT_ROUND: 
                                          // TODO check differenc between RAT_TO_INT and RAT_FLOOR
    case Interpretation::INT_TO_INT:
    case Interpretation::INT_FLOOR:       return fn([](auto ts) { return ts[0]; });

    case Interpretation::INT_QUOTIENT_F:  return fn(quotientF);
    case Interpretation::INT_REMAINDER_F: return fn(remainder(quotientF));

    case Interpretation::INT_QUOTIENT_E:  return fn(quotientE);
    case Interpretation::INT_REMAINDER_E: return fn(remainder(quotientE));

    case Interpretation::INT_QUOTIENT_T:
    case Interpretation::INT_REMAINDER_T:
    case Interpretation::INT_ABS:
        ASSERTION_VIOLATION_REP("TODO: look up the semantics of this and implement a translation")
        return {};

    case Interpretation::RAT_UNARY_MINUS:
    case Interpretation::RAT_PLUS:
    case Interpretation::RAT_MINUS:
    case Interpretation::RAT_MULTIPLY:
    case Interpretation::RAT_QUOTIENT:
    case Interpretation::RAT_QUOTIENT_E:
    case Interpretation::RAT_QUOTIENT_T:
    case Interpretation::RAT_QUOTIENT_F:
    case Interpretation::RAT_REMAINDER_E:
    case Interpretation::RAT_REMAINDER_T:
    case Interpretation::RAT_REMAINDER_F:
    case Interpretation::RAT_FLOOR:
    case Interpretation::RAT_ROUND:

    case Interpretation::REAL_UNARY_MINUS:
    case Interpretation::REAL_PLUS:
    case Interpretation::REAL_MINUS:
    case Interpretation::REAL_MULTIPLY:
    case Interpretation::REAL_QUOTIENT:
    case Interpretation::REAL_QUOTIENT_E:
    case Interpretation::REAL_QUOTIENT_T:
    case Interpretation::REAL_QUOTIENT_F:
    case Interpretation::REAL_REMAINDER_E:
    case Interpretation::REAL_REMAINDER_T:
    case Interpretation::REAL_REMAINDER_F:
    case Interpretation::REAL_FLOOR:
    case Interpretation::REAL_ROUND:

    case Interpretation::INT_TO_RAT:
    case Interpretation::INT_TO_REAL:
    case Interpretation::RAT_TO_INT:
    case Interpretation::RAT_TO_RAT:
    case Interpretation::RAT_TO_REAL:
    case Interpretation::REAL_TO_INT:
    case Interpretation::REAL_TO_RAT:
    case Interpretation::REAL_TO_REAL:

      // array functions
    case Interpretation::ARRAY_SELECT:
    case Interpretation::ARRAY_STORE:
        ASSERTION_VIOLATION_REP("TODO integrate with arrays")
        return {};

    case Interpretation::INVALID_INTERPRETATION:
    case Interpretation::ARRAY_BOOL_SELECT:
        ASSERTION_VIOLATION_REP("not a function interpretation")
        return {};

    case Interpretation::REAL_TRUNCATE:
    case Interpretation::RAT_TRUNCATE:
        ASSERTION_VIOLATION_REP("TODO: translated to ite + floor")
        return {};
    case Interpretation::REAL_CEILING:
    case Interpretation::RAT_CEILING:
        ASSERTION_VIOLATION_REP("TODO: this should translate to -floor(-x)")
        return {};
    }
}
Option<std::function<Literal*(TermList*)>> translateInterpretedPredicate(unsigned f)
{
  if(!theory->isInterpretedPredicate(f))
    return {};

  auto fn = [](auto x) { return some(std::function<Literal*(TermList*)>(std::move(x))); };

  switch(theory->interpretPredicate(f)) {
    case Interpretation::EQUAL: return fn([](auto x) -> Literal* { ASSERTION_VIOLATION_REP("this should never be called bc alas equality is special") });

    case Interpretation::INT_IS_INT:  
    case Interpretation::INT_IS_RAT: 
    case Interpretation::INT_IS_REAL: 
        ASSERTION_VIOLATION_REP("TODO")
      return {};

    case Interpretation::INT_GREATER:       return fn([](auto ts){ return R::greater(true, ts[0], ts[1]); });
    case Interpretation::INT_GREATER_EQUAL: return fn([](auto ts){ return R::geq    (true, ts[0], ts[1]); });
    case Interpretation::INT_LESS:          return fn([](auto ts){ return R::less   (true, ts[0], ts[1]); }); 
    case Interpretation::INT_LESS_EQUAL:    return fn([](auto ts){ return R::leq    (true, ts[0], ts[1]); }); 
    case Interpretation::INT_DIVIDES:       return fn([](auto ts){ return R::isInt  (true, R::div(ts[1], ts[0])); });

    case Interpretation::RAT_IS_INT:
    case Interpretation::RAT_IS_RAT:
    case Interpretation::RAT_IS_REAL:
    case Interpretation::RAT_GREATER:
    case Interpretation::RAT_GREATER_EQUAL:
    case Interpretation::RAT_LESS:
    case Interpretation::RAT_LESS_EQUAL:
    case Interpretation::REAL_IS_INT:
    case Interpretation::REAL_IS_RAT:
    case Interpretation::REAL_IS_REAL:
    case Interpretation::REAL_GREATER:
    case Interpretation::REAL_GREATER_EQUAL:
    case Interpretation::REAL_LESS:
    case Interpretation::REAL_LESS_EQUAL:
      return {};
    case Interpretation::ARRAY_BOOL_SELECT:
      ASSERTION_VIOLATION_REP("TODO integrate with arrays")
      return {};

    case Interpretation::INT_SUCCESSOR:
    case Interpretation::INT_UNARY_MINUS:
    case Interpretation::INT_PLUS:
    case Interpretation::INT_MINUS:
    case Interpretation::INT_MULTIPLY:
    case Interpretation::INT_QUOTIENT_E:
    case Interpretation::INT_QUOTIENT_T:
    case Interpretation::INT_QUOTIENT_F:
    case Interpretation::INT_REMAINDER_E:
    case Interpretation::INT_REMAINDER_T:
    case Interpretation::INT_REMAINDER_F:
    case Interpretation::INT_FLOOR:
    case Interpretation::INT_CEILING:
    case Interpretation::INT_TRUNCATE:
    case Interpretation::INT_ROUND:
    case Interpretation::INT_ABS:
    case Interpretation::INT_TO_INT:
    case Interpretation::INT_TO_RAT:
    case Interpretation::INT_TO_REAL:
    case Interpretation::ARRAY_SELECT:
    case Interpretation::ARRAY_STORE:
    case Interpretation::RAT_UNARY_MINUS:
    case Interpretation::RAT_PLUS:
    case Interpretation::RAT_MINUS:
    case Interpretation::RAT_MULTIPLY:
    case Interpretation::RAT_QUOTIENT:
    case Interpretation::RAT_QUOTIENT_E:
    case Interpretation::RAT_QUOTIENT_T:
    case Interpretation::RAT_QUOTIENT_F:
    case Interpretation::RAT_REMAINDER_E:
    case Interpretation::RAT_REMAINDER_T:
    case Interpretation::RAT_REMAINDER_F:
    case Interpretation::RAT_FLOOR:
    case Interpretation::RAT_CEILING:
    case Interpretation::RAT_TRUNCATE:
    case Interpretation::RAT_ROUND:
    case Interpretation::REAL_UNARY_MINUS:
    case Interpretation::REAL_PLUS:
    case Interpretation::REAL_MINUS:
    case Interpretation::REAL_MULTIPLY:
    case Interpretation::REAL_QUOTIENT:
    case Interpretation::REAL_QUOTIENT_E:
    case Interpretation::REAL_QUOTIENT_T:
    case Interpretation::REAL_QUOTIENT_F:
    case Interpretation::REAL_REMAINDER_E:
    case Interpretation::REAL_REMAINDER_T:
    case Interpretation::REAL_REMAINDER_F:
    case Interpretation::REAL_FLOOR:
    case Interpretation::REAL_CEILING:
    case Interpretation::REAL_TRUNCATE:
    case Interpretation::REAL_ROUND:
    case Interpretation::RAT_TO_INT:
    case Interpretation::RAT_TO_RAT:
    case Interpretation::RAT_TO_REAL:
    case Interpretation::REAL_TO_INT:
    case Interpretation::REAL_TO_RAT:
    case Interpretation::REAL_TO_REAL:
    case Interpretation::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION_REP("not a predicate interpretation")
      return {};
    }
}

void InequalityNormalizer::realization(Problem& p)
{
  auto trans = tranlateSignature();
  auto& fs  = trans.first;
  auto& ps  = trans.second;
  auto translateTerm = [&](TermList t) -> TermList { 
    return evalBottomUp<TermList>(t, [&](auto orig, auto* evalArgs) {
        if (orig.isVar()) {
          return orig;
        } else {
          auto f = orig.term()->functor();
          auto itp = translateInterpretedFunction(f);
          if (itp) {
            return (*itp)(evalArgs);
          } else {
            return TermList(Term::create(fs[f], orig.term()->arity(), evalArgs));
          }
        }
    });
  };
  auto translateLit = [&](Literal* lit) -> Literal* {
    auto p = lit->functor();
    if (lit->isEquality()) {
      auto s = SortHelper::getEqualityArgumentSort(lit);
      return Literal::createEquality(lit->polarity(), translateTerm(lit->termArg(0)), translateTerm(lit->termArg(1)), s == IntTraits::sort() ? R::sort() : s);
    }
    auto itp = translateInterpretedPredicate(p);

    Recycled<Stack<TermList>> args;
    args->loadFromIterator(
        anyArgIter(lit).map([&](auto arg) { return translateTerm(arg); }));
    if (itp) {
      auto res = (*itp)(args->begin());
      return lit->polarity() != res->polarity() ? Literal::complementaryLiteral(res) : res;
    } else {
      return Literal::createFromIter(
          lit->polarity(),
          ps[lit->functor()], 
          args->iterFifo()
          );
    }

  };
  p.mapUnits([&](auto c_) {
      Recycled<Stack<Unit*>> out;
      ASS(c_->isClause());
      auto c =  static_cast<Clause*>(c_);
      Recycled<Stack<Literal*>> clOut;
      
      for (auto l : iterTraits(c->iterLits())) {
        

        auto itp = normalizeLasca<IntTraits>(l);
        if (itp) {
          for (auto nl : itp->value) {
            clOut->push(R::isInt(false, translateTerm(nl.term().denormalize())));
          }
        }
        clOut->push(translateLit(l));
      }

      out->push(Clause::fromStack(*clOut, 
          Inference(FormulaTransformation(InferenceRule::ALASCAI_REALIZATION, c))));


      return out;
  });

  // TODO replace these axioms by rules (?)
  auto x = TermList::var(0);

  p.units() = 
    /* isInt(x) -> toInt(x) == x */
        UnitList::cons(Clause::fromStack({ R::isInt(false, x), R::eq(true, x, R::toInt(x))}, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
    /* 0 <= x - toInt(x) */
      , UnitList::cons(Clause::fromStack({ R::leq(true, R::zero(), R::add(x, R::minus(R::toInt(x)))) }, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
    /* x - toInt(x) < 1 */
      , UnitList::cons(Clause::fromStack({ R::less(true, R::add(x, R::minus(R::toInt(x))), R::one()) }, Inference(TheoryAxiom(InferenceRule::THA_ALASCAI)))
      , p.units())))
    ;

  for (auto i : range(0, fs.size())) {
    auto f = fs[i];
    Recycled<Stack<TermList>> args;
    if (f != unsigned(-1) && f != i) {
      // ^^^^^^^^^^^^^^^     ^^^^^^-> has been transformed
      //     \->not interpreted

      auto arity = env.signature->getFunction(f)->arity();
      while(args->size() < arity) {
        args->push(TermList::var(args->size()));
      }

      // adding isInt(f(x1, ..., xn))
      auto cl = Clause::fromStack({ R::isInt(true, TermList(Term::create(f, arity, args->begin()))) }, Inference(TheoryAxiom(InferenceRule::ALASCAI_REALIZATION_AXIOM)));
      p.units() = UnitList::cons(cl, p.units());
    }
  }

}

pair<Stack<unsigned>, Stack<unsigned>> InequalityNormalizer::tranlateSignature()
{
  Stack<unsigned> fs;

  auto reals = R::sort();
  auto ints  = IntTraits::sort();

  auto iterArgs = [&](OperatorType* o)  
    { return range(0, o->arity())
               .map([=](auto i) { return o->arg(i); }); };


  auto mappedArgs = [&](OperatorType* o)  { 
      Recycled<Stack<TermList>> out;
      out->loadFromIterator(iterArgs(o)
          .map([&](auto a) {  return a == ints ? reals : a; }));
      return out;
    };

  auto hasIntArgs = [&](OperatorType* o)  
    { return iterArgs(o).any([&](auto a) { return a == ints; }); };

  for (auto f : range(0, env.signature->functions())) {
    auto f_ = translateInterpretedFunction(f);
    if (f_) {
      fs.push(unsigned(-1)); // <- dummy. should never be accessed
    } else {
      auto sym = env.signature->getFunction(f);
      auto op = sym->fnType();
      if (hasIntArgs(op) || op->result() == ints) {
        Recycled<Stack<TermList>> args = mappedArgs(op);
        auto res = op->result() == ints ? reals : op->result();
        
        fs.push(env.signature->addFreshFunction(
                OperatorType::getFunctionType(*args, res), 
                sym->name().c_str()));
      } else {
        fs.push(f);
      }
    }
  }

  Stack<unsigned> ps;
  for (auto p : range(0, env.signature->predicates())) {
    auto p_ = translateInterpretedPredicate(p);
    if (p_) {
      ps.push(-1); // <- dummy. should never be accessed
    } else {
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
  }
  return make_pair(std::move(fs), std::move(ps));
}

} // namespace Kernel

