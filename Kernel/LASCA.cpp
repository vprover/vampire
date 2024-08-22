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
#include "Lib/Recycled.hpp"
#include "Lib/Stack.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/QKbo.hpp"
// #include "Kernel/LaLpo.hpp"


#define DEBUG(...) // DBG(__VA_ARGS__)
#define DEBUG_TRANSLATION(...) // DBG(__VA_ARGS__)
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
        .any([&](auto s) { return maybeEquiv(s, term); })) 
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
  Stack<TermList> args(lit->arity());
  args.loadFromIterator(typeArgIter(lit));
  for (auto orig : termArgIter(lit)) {
    if (orig.isVar()) {
      args.push(orig);
    } else {
      auto norm = PolyNf::normalize(TypedTermList(orig.term()));
      auto eval = evaluator()
        .evaluate(norm)
        .map([](auto t) { return t.denormalize(); }) 
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
          arrayIter(*norm)
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
std::shared_ptr<LascaState> testLascaState(Options::UnificationWithAbstraction uwa, bool strongNormalization, Ordering* ordering, bool uwaFixedPointIteration) {

  auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/* rand */false, /*qkbo*/ true)) : nullptr;
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

Option<AnyLascaLiteral> InequalityNormalizer::renormalize(Literal* lit) const
{
  using Out = AnyLascaLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto x) { return Out(x); });
  };
  return             wrapCoproduct(renormalizeLasca< IntTraits>(lit))
    || [&](){ return wrapCoproduct(renormalizeLasca< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(renormalizeLasca<RealTraits>(lit)); } 
    || Option<Out>();
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
        return Option<AnyLascaLiteral>(res);
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
  return out || norm;
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

/**
 * Class that uses @c NLiteralTransformer to perform transformations on formulas
 */
class IntegerConversionFT : public FormulaTransformer
{
  LascaPreprocessor& _self;
public:
  IntegerConversionFT(LascaPreprocessor& self) : _self(self) {}

protected:
  /**
   * Transfor atomic formula
   *
   * The rest of transformations is done by the @c FormulaTransformer ancestor.
   */
  virtual Formula* applyLiteral(Formula* f)
  {
    Literal* l = f->literal();
    auto ll = _self.integerConversion(l);
    return l == ll ? f : new AtomicFormula(ll);
  }
};

unsigned LascaPreprocessor::integerFunctionConversion(unsigned f) {
  return _funcs.getOrInit(f, [&]() { 
    using Z = IntTraits;
    using R = RealTraits;
    if (Z::isAdd(f)) return R::addF();
    if (Z::isMul(f)) return R::mulF();
    if (Z::isMinus(f)) return R::minusF();
    ASS(!R::isToInt(f))
    // if (Z::isFloor(f)) return R::floorF();
    // if (R::isToInt(f)) return R::floorF();
    if (auto n = Z::tryNumeral(f)) return R::numeralF(typename R::ConstantType(*n));
    // TODO 
    // INT_SUCCESSOR,
    // INT_MINUS, (binary minus)// difference in TPTP
    // INT_QUOTIENT_E,
    // INT_QUOTIENT_T,
    // INT_QUOTIENT_F,
    // INT_REMAINDER_E,
    // INT_REMAINDER_T,
    // INT_REMAINDER_F,
    // INT_CEILING,
    // INT_TRUNCATE,
    // INT_ROUND,
    // INT_ABS,

    auto sorts_changed = false;
    auto intConv= [&](auto x) { 
      auto out = integerConversion(TypedTermList(x, AtomicSort::superSort())); 
      sorts_changed |= out != x;
      return out;
    };

    auto sym = env.signature->getFunction(f);
    auto ty = sym->fnType();
    Recycled<Stack<TermList>> sorts;
    for (auto i : range(0, ty->arity())) {
      sorts->push(intConv(ty->arg(i)));
    }
    auto res_sort = intConv(ty->result());
    if (sorts_changed) {
      unsigned nf = env.signature->addFreshFunction(sym->arity(), sym->name().c_str());
      auto nsym = env.signature->getFunction(nf);
      auto nty = OperatorType::getFunctionType(sym->arity(), sorts->begin(), res_sort, ty->numTypeArguments());
      nsym->setType(nty);
      DEBUG_TRANSLATION(*sym, ": ", ty->toString(), " -> ", *nsym, ": ", nty->toString());
      return nf;
    } else {
      return f;
    }
  });
}


unsigned LascaPreprocessor::integerTypeConsConversion(unsigned f) {
  if (env.signature->getIntSort() == f) { return env.signature->getRealSort(); }
  return f;
}


unsigned LascaPreprocessor::integerPredicateConversion(unsigned f) {

  return _preds.getOrInit(f, [&]() { 
    using Z = IntTraits;
    using R = RealTraits;
    if (Z::isLess(f)) return R::lessF();
    if (Z::isLeq(f)) return R::leqF();
    if (Z::isGreater(f)) return R::greaterF();
    if (Z::isGeq(f)) return R::geqF();
    // TODO divides

    auto sym = env.signature->getPredicate(f);
    auto ty = sym->predType();
    auto sorts_changed = false;
    auto intConv= [&](auto x) { 
      auto out = integerConversion(TypedTermList(x, AtomicSort::superSort())); 
      sorts_changed |= out != x;
      return out;
    };
    Recycled<Stack<TermList>> arg_sorts;
    for (auto i : range(0, ty->arity())) {
      arg_sorts->push(intConv(ty->arg(i)));
    }
    if (sorts_changed) {
      unsigned nf = env.signature->addFreshPredicate(sym->arity(), sym->name().c_str());
      auto nsym = env.signature->getPredicate(nf);
      auto nty = OperatorType::getPredicateType(sym->arity(), arg_sorts->begin(), ty->numTypeArguments());
      nsym->setType(nty);
      DEBUG_TRANSLATION(*sym, ": ", ty->toString(), " -> ", *nsym, ": ", nty->toString());
      return nf;
    } else {
      return f;
    }
  });
}

// unsigned LascaPreprocessor::integerFunctionConversion(unsigned f) {
//
// }
// unsigned LascaPreprocessor::integerTypeConsConversion(unsigned f) {
//
// }


TermList LascaPreprocessor::integerConversion(TypedTermList t)
{
  return BottomUpEvaluation<TypedTermList, TermList>()
    .function([this](TypedTermList t, TermList* args) -> TermList {
        if (t.isVar()) {
          return t;
        } else {
          auto f = t.term()->functor();
          if (t.sort() == AtomicSort::superSort()) {
            return TermList(AtomicSort::create(this->integerTypeConsConversion(f), t.term()->arity(), args));
          } else {
            if (IntTraits::isToReal(f) || IntTraits::isToInt(f) || RealTraits::isToReal(f)) {
              return args[0];
            } if (RealTraits::isToInt(f)) {
              return TermList(RealTraits::floor(args[0]));
            } else {
              auto out = TermList(Term::create(this->integerFunctionConversion(f), t.term()->arity(), args));
              return t.sort() == IntTraits::sort() ? RealTraits::floor(out) : out;
            }
          }
        }
    })
    .context(Lib::TermListContext{ .ignoreTypeArgs = false, })
    .apply(t);
}

Literal* LascaPreprocessor::integerConversion(Literal* lit)
{
  auto impl = [&]() { 
    if (lit->isEquality()) {
      auto sort = SortHelper::getEqualityArgumentSort(lit);
      return Literal::createEquality(lit->polarity(), 
          integerConversion(TypedTermList(lit->termArg(0), sort)), 
          integerConversion(TypedTermList(lit->termArg(1), sort)), 
          integerConversion(TypedTermList(sort, AtomicSort::superSort())));
    } else {
      auto ff = integerPredicateConversion(lit->functor());
      Recycled<Stack<TermList>> args;
      for (auto a : anyArgIterTyped(lit)) {
        args->push(integerConversion(a));
      }
      return Literal::create(ff, args->size(), lit->polarity(), lit->commutative(), args->begin());
    }
  };
  auto out = impl();
  if (out != lit) {
    DEBUG_TRANSLATION(*lit, " ==> ", *out);
  }
  return out;
}


Clause* LascaPreprocessor::integerConversion(Clause* clause)
{
  auto change = false;
  Recycled<Stack<Literal*>> res;
  for (auto l : clause->iterLits()) {
    auto ll = integerConversion(l);
    change |= ll != l;
    res->push(ll);
  }
  if (change) {
    return Clause::fromStack(*res, Inference(FormulaTransformation(INF_RULE, clause)));
  } else {
    return clause;
  }
}
FormulaUnit* LascaPreprocessor::integerConversion(FormulaUnit* unit)
{
  IntegerConversionFT ftrans(*this);
  FTFormulaUnitTransformer<decltype(ftrans)> futrans(INF_RULE, ftrans);
  return futrans.transform(unit);
}

} // namespace Kernel

