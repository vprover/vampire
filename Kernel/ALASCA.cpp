/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ALASCA.hpp"
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

bool isInequality(AlascaPredicate const& self) 
{
  switch(self) {
    case AlascaPredicate::EQ: 
    case AlascaPredicate::NEQ: return false;
    case AlascaPredicate::GREATER: 
    case AlascaPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}

std::ostream& operator<<(std::ostream& out, AlascaPredicate const& self)
{ 
  switch(self) {
    case AlascaPredicate::EQ: return out << "==";
    case AlascaPredicate::NEQ: return out << "!=";
    case AlascaPredicate::GREATER: return out << ">";
    case AlascaPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
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
      auto eval = _eval
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
      auto norm = normalizeAlasca<decltype(numTraits)>(lit);
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

#if VDEBUG
std::shared_ptr<AlascaState> testAlascaState(Options::UnificationWithAbstraction uwa, std::shared_ptr<InequalityNormalizer> norm, Ordering* ordering, bool uwaFixedPointIteration) {

  auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/* rand */false, /*qkbo*/ true), norm) : nullptr;
  auto& ord = ordering == nullptr ? *qkbo : *ordering;
  return AlascaState::create(norm, &ord, uwa, uwaFixedPointIteration);
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

Option<AnyAlascaLiteral> InequalityNormalizer::renormalize(Literal* lit) const
{
  using Out = AnyAlascaLiteral;
  auto wrapCoproduct = [](auto&& norm) {
    return std::move(norm).map([](auto x) { return Out(x); });
  };
  return             wrapCoproduct(renormalizeAlasca< IntTraits>(lit))
    || [&](){ return wrapCoproduct(renormalizeAlasca< RatTraits>(lit)); } 
    || [&](){ return wrapCoproduct(renormalizeAlasca<RealTraits>(lit)); } 
    || Option<Out>();
}

// Stack<std::pair<Literal*, unsigned>> AlascaState::selectedLiteralsWithIdx(Clause* cl, bool strictlyMax)
// {
//   return iterTraits(getRangeIterator((unsigned)0, cl->numSelected()))
//     .map([=](auto i) 
//         { return make_pair((*cl)[i], i); })
//     .template collect<Stack>();
// }
//
//
// Stack<Literal*> AlascaState::selectedLiterals(Clause* cl, bool strictlyMax)
// {
//   // TODO use strictly max
//   return iterTraits(cl->getSelectedLiteralIterator()).template collect<Stack>();
// }
//
//
// Stack<std::pair<Literal*, unsigned>> AlascaState::maxLiteralsWithIdx(Clause* cl, bool strictlyMax)
// {
//   return maxElements([&](unsigned i) { return make_pair((*cl)[i], i); }, 
//                      cl->size(),
//                      [&](auto l, auto r) { return ordering->compare(l.first, r.first); },
//                      strictlyMax);
// }
//
//
// Stack<Literal*> AlascaState::maxLiterals(Clause* cl, bool strictlyMax)
// {
//   return maxElements([&](auto i) { return (*cl)[i]; }, 
//                      cl->size(),
//                      [&](auto l, auto r) { return ordering->compare(l, r); },
//                      strictlyMax);
// }
//
//
// Stack<Literal*> AlascaState::maxLiterals(Stack<Literal*> cl, bool strictlyMax)
// {
//   return maxElements([&](auto i) { return cl[i]; }, 
//                      cl.size(),
//                      [&](auto l, auto r) { return ordering->compare(l, r); },
//                      strictlyMax);
// }



Option<AnyInequalityLiteral> InequalityNormalizer::renormalizeIneq(Literal* lit)
{
  return renormalize(lit)
    .andThen([](auto res) {
      return res.apply([](auto lit) { 
          return inequalityLiteral(lit).map([](auto x) { return AnyInequalityLiteral(x); }); 
      });
    });
}

Option<AbstractingUnifier> AlascaState::unify(TermList lhs, TermList rhs) const 
{ return AbstractingUnifier::unify(lhs, 0, rhs, 0, uwaMode(), uwaFixedPointIteration); }

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect)
{ return toCorrect.intDivide(gcd); }


IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r)
{ return l.gcd(r); }

Ordering::Result compare(AlascaPredicate l, AlascaPredicate r) 
{
       if (l < r)  return Ordering::Result::LESS;
  else if (l > r)  return Ordering::Result::GREATER;
  else if (l == r) return Ordering::Result::EQUAL;
  else ASSERTION_VIOLATION
}

SelectedLiteral::SelectedLiteral(Clause* clause, unsigned litIdx, AlascaState& shared)
  : cl(clause)
  , litIdx(litIdx)
  , interpreted(shared.norm().renormalize(literal()))
{}

std::shared_ptr<AlascaState> AlascaState::globalState = nullptr;
std::shared_ptr<InequalityNormalizer> InequalityNormalizer::globalNormalizer = nullptr;

unsigned AlascaPreprocessor::integerFunctionConversion(unsigned f) {
  return _funcs.getOrInit(f, [&]() { 
    if (Z::isAdd(f)) return R::addF();
    if (Z::isMul(f)) return R::mulF();
    if (Z::isMinus(f)) return R::minusF();
    ASS(!R::isToInt(f))
    if (auto n = Z::tryNumeral(f)) return R::numeralF(typename R::ConstantType(*n));
    // TODO 
#define ASS_NOT(itp) ASS(!theory->isInterpretedFunction(f, itp))
    ASS_NOT(Theory::INT_SUCCESSOR)
    ASS_NOT(Theory::INT_QUOTIENT_E)
    ASS_NOT(Theory::INT_QUOTIENT_T)
    ASS_NOT(Theory::INT_QUOTIENT_F)
    ASS_NOT(Theory::INT_REMAINDER_E)
    ASS_NOT(Theory::INT_REMAINDER_T)
    ASS_NOT(Theory::INT_REMAINDER_F)
    ASS_NOT(Theory::INT_CEILING)
    ASS_NOT(Theory::INT_TRUNCATE)
    ASS_NOT(Theory::INT_ROUND)
    ASS_NOT(Theory::INT_ABS)
#undef ASS_NOT

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


unsigned AlascaPreprocessor::integerTypeConsConversion(unsigned f) {
  if (env.signature->getIntSort() == f) { return env.signature->getRealSort(); }
  return f;
}


unsigned AlascaPreprocessor::integerPredicateConversion(unsigned f) {

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

// unsigned AlascaPreprocessor::integerFunctionConversion(unsigned f) {
//
// }
// unsigned AlascaPreprocessor::integerTypeConsConversion(unsigned f) {
//
// }


TermList AlascaPreprocessor::integerConversion(TypedTermList t)
{
  return BottomUpEvaluation<TypedTermList, TermList>()
    .function([this](TypedTermList t, TermList* args) -> TermList {
        auto wrapFloor = _useFloor && t.sort() == IntTraits::sort();
        if (t.isVar()) {
          return wrapFloor ?  RealTraits::floor(t) : t;
        } else {
          auto f = t.term()->functor();
          if (t.sort() == AtomicSort::superSort()) {
            return  t == AtomicSort::superSort() ? t
                  : TermList(AtomicSort::create(this->integerTypeConsConversion(f), t.term()->arity(), args));
          } else {
            if (IntTraits::isToReal(f) || IntTraits::isToInt(f) || RealTraits::isToReal(f)) {
              return args[0];
            } else if (RealTraits::isToInt(f)) {
              return TermList(RealTraits::floor(args[0]));
            } else {
              auto out = TermList(Term::create(this->integerFunctionConversion(f), t.term()->arity(), args));
              return wrapFloor ? RealTraits::floor(out) : out;
            }
          }
        }
    })
    .context(Lib::TermListContext{ .ignoreTypeArgs = false, })
    .apply(t);
}

Literal* AlascaPreprocessor::integerConversion(Literal* lit)
{
  // AlascaState::globalState->normalizer->normalizeLiteral()
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
      return Literal::create(ff, args->size(), lit->polarity(), args->begin());
    }
  };
  auto out = impl();
  if (out != lit) {
    DEBUG_TRANSLATION(*lit, " ==> ", *out);
  }
  return out;
}


Clause* AlascaPreprocessor::integerConversion(Clause* clause)
{
  auto notInt = [](auto t) { return R::eq(false, t, R::floor(t)); };
  auto change = false;
  Recycled<Stack<Literal*>> res;
  for (auto l : clause->iterLits()) {
    auto ll = integerConversion(l);
    change |= ll != l;
    if (!_useFloor) {
      if (l->isEquality() && l->eqArgSort() == Z::sort()) {
        ASS(ll->isEquality() && ll->eqArgSort() == R::sort() && change)
        res->pushMany(notInt(ll->termArg(0)), notInt(ll->termArg(1)));
      } else if (l->functor() != ll->functor() && theory->isInterpretedPredicate(ll->functor())) {
        ASS(ll->arity() == l->arity())
        res->loadFromIterator(range(0, l->numTermArguments())
            .filter([&](auto i) { return SortHelper::getTermArgSort(l, i) == Z::sort(); })
            .map([&](auto i) { return notInt(ll->termArg(i)); }));
      }
    }
    res->push(ll);
  }
  if (change) {
    return Clause::fromStack(*res, Inference(FormulaTransformation(INF_RULE, clause)));
  } else {
    return clause;
  }
}

void AlascaPreprocessor::integerConversion(Problem& prb)
{
  for (auto& unit : iterTraits(prb.units()->iter())) {
    unit = integerConversion(unit);
  }
  if (!_useFloor) {
    for (auto& func : iterTraits(_funcs.iter())) {
      auto orig_sym = env.signature->getFunction(func.key());
      if (!theory->isInterpretedFunction(func.value()) && !R::isNumeral(func.value())) {
        auto sym = env.signature->getFunction(func.value());
        if (orig_sym->fnType()->result() == Z::sort()) {
          auto t = TermList(Term::createFromIter(func.value(), range(0, sym->arity()).map([](auto x) { return TermList::var(x); })));
          // TODO use something else than NonspecificInferenceMany
          auto inf = Inference(NonspecificInferenceMany(INF_RULE, nullptr));
          auto cl = Clause::fromLiterals({R::eq(true, R::floor(t), t)}, inf);
          UnitList::push(cl, prb.units());
        }
      }
    }
  }
  
}

} // namespace Kernel

