/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * Defines functions and structures that are shared by all ALASCA inference rules in order to select literals, terms, etc.
 */

#ifndef __ALASCA_Preprocessor__
#define __ALASCA_Preprocessor__

#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Formula.hpp"

#define DEBUG_TRANSLATION(...) // DBG(__VA_ARGS__)

namespace Kernel {

class AlascaPreprocessor 
{
  std::shared_ptr<InequalityNormalizer> _norm;
  Map<unsigned, unsigned> _preds;
  Map<unsigned, unsigned> _funcs;
  // TODO create option for this
  bool _useFloor = false;

  using Z = IntTraits;
  using R = RealTraits;
  static constexpr InferenceRule INF_RULE = InferenceRule::ALASCA_INTEGER_TRANSFORMATION;

  Literal* integerConversion(Literal* l)
  {
    auto lit = _norm->normalizedLiteral(l);
    // AlascaState::globalState->normalizer->normalizedLiteral()
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

  TermList integerConversion(TypedTermList t) 
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
              auto rem = [](auto quot, auto l, auto r) { return R::add(l, R::minus(R::mul(r,quot(l,r)))); };
              auto quotF = [](auto l, auto r) { return R::floor(R::div(l,r)); };
              if (IntTraits::isToReal(f) || IntTraits::isToInt(f) || RealTraits::isToReal(f)) {
                return args[0];
              } else if (Z::isRemainderF(f) || R::isRemainderF(f)) {
                return rem(quotF,args[0], args[1]);
              } else if (Z::isQuotientF(f) || R::isQuotientF(f)) {
                return quotF(args[0], args[1]);
              } else if (R::isToInt(f)) {
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

  unsigned integerPredicateConversion(unsigned f)
  {

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

  unsigned integerFunctionConversion(unsigned f)
  {
    return _funcs.getOrInit(f, [&]() { 
      if (Z::isAdd(f)) return R::addF();
      if (Z::isMul(f)) return R::mulF();
      if (Z::isMinus(f)) return R::minusF();
      ASS(!R::isToInt(f))
      if (auto n = Z::tryLinMul(f)) return R::linMulF(typename R::ConstantType(*n));
      if (auto n = Z::tryNumeral(f)) return R::numeralF(typename R::ConstantType(*n));
      // TODO 
#define ASS_NOT(itp) ASS(!theory->isInterpretedFunction(f, itp))
      ASS_NOT(Theory::INT_SUCCESSOR)
      ASS_NOT(Theory::INT_QUOTIENT_T)
      ASS_NOT(Theory::INT_REMAINDER_T)
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

  unsigned integerTypeConsConversion(unsigned f)
  {
    if (env.signature->getIntSort() == f) { return env.signature->getRealSort(); }
    return f;
  }

  Clause* integerConversion(Clause* clause)
  {
    auto notInt = [&](auto t) -> Option<Literal*> { 
      if (auto q = R::tryNumeral(t)) {
        if (q->isInt()) {
          return {};
        }
      }
      return some(R::eq(false, t, R::floor(t))); 
    };
    auto change = false;
    Recycled<Stack<Literal*>> res;
    for (auto l : clause->iterLits()) {
      auto ll = integerConversion(l);
      change |= ll != l;
      if (!_useFloor) {
        if (l->isEquality() && l->eqArgSort() == Z::sort()) {
          ASS(ll->isEquality() && ll->eqArgSort() == R::sort() && change)
          res->loadFromIterator(termArgIter(ll)
              .filterMap([&](auto x) { return notInt(x); }));
        } else if (l->functor() != ll->functor() && theory->isInterpretedPredicate(ll->functor())) {
          ASS(ll->arity() == l->arity())
          res->loadFromIterator(range(0, l->numTermArguments())
              .filter([&](auto i) { return SortHelper::getTermArgSort(l, i) == Z::sort(); })
              .filterMap([&](auto i) { return notInt(ll->termArg(i)); }));
        }
      }
      res->push(ll);
    }
    if (change) {
      return Clause::fromStack(*res, Inference(FormulaClauseTransformation(INF_RULE, clause)));
    } else {
      return clause;
    }
  }

  Unit* integerConversion(Unit* unit) {
    ASS_REP(unit->isClause(), "integer conversion needs to be performed after clausification because we don't wanna deal with FOOL & friends here")
    return (Unit*)integerConversion(static_cast<Clause*>(unit));
  }
public:


  AlascaPreprocessor(std::shared_ptr<InequalityNormalizer> norm) 
    : _norm(std::move(norm))
    , _preds()
    , _funcs() {}

  void integerConversion(Problem& prb)
  {
    for (auto& unit : iterTraits(prb.units()->iter())) {
      unit = integerConversion(unit);
    }
    if (!_useFloor) {
      for (auto& func : iterTraits(_funcs.iter())) {
        auto orig_sym = env.signature->getFunction(func.key());
        if (!theory->isInterpretedFunction(func.value()) 
            && !R::isNumeral(func.value())
            && !R::isLinMul(func.value())
            ) {
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
};

class QuotientEPreproc 
{
  bool _addedITE = false;
  using Z = IntTraits;
  // TODO
  static constexpr InferenceRule INF_RULE = InferenceRule::ALASCA_INTEGER_TRANSFORMATION;

  Literal* proc(Literal* lit)
  {
    auto impl = [&]() { 
      if (lit->isEquality()) {
        auto sort = SortHelper::getEqualityArgumentSort(lit);
        return Literal::createEquality(lit->polarity(), 
            proc(TypedTermList(lit->termArg(0), sort)), 
            proc(TypedTermList(lit->termArg(1), sort)), 
            sort);
      } else {
        auto ff = lit->functor();
        Recycled<Stack<TermList>> args;
        args->loadFromIterator(typeArgIter(lit));
        for (auto a : termArgIterTyped(lit)) {
          args->push(proc(a));
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

  TermList transformSubterm(TermList t) {
    if (!t.isTerm()) return t;
    if (t.term()->isSpecial()) return t;
    auto &trm = *t.term();

    auto ite = [](auto c, auto x, auto y) {
      return TermList(Term::createITE(new AtomicFormula(c), x, y, Z::sort()));
    };
    auto transQuotientE = [&]() {
      return ite(Z::greater(true, trm.termArg(1),  Z::constantTl(0)), Z::quotientF(trm.termArg(0), trm.termArg(1)),
             ite(Z::less(true, trm.termArg(1), Z::constantTl(0)), Z::minus(Z::quotientF(Z::minus(trm.termArg(0)), trm.termArg(1))),
              Z::quotientE(trm.termArg(0), Z::zero())
      ));
    };
    if (Z::isQuotientE(t) && trm.termArg(1) != Z::zero()) {
      _addedITE = true;
      return transQuotientE();
    } else if (Z::isRemainderE(t)) {
      _addedITE = true;
      // quot * arg[1] + rem = arg[0]
      // rem = arg[0] - quot * arg[1]
      return Z::add(trm.termArg(0), Z::minus(Z::mul(trm.termArg(1), transQuotientE())));
    } else {
      return t;
    }
  }

  TermList proc(TypedTermList t) 
  {
    auto trans = TermTrans(*this);
    return t.isVar() ? t : TermList(trans.transform(t.term()));
  }

  Clause* proc(Clause* clause)
  {
    auto change = false;
    RStack<Literal*> res;
    for (auto lit : clause->iterLits()) {
      auto ll = proc(lit);
      change |= ll != lit;
      res->push(ll);
    }
    if (change) {
      return Clause::fromStack(*res, Inference(FormulaClauseTransformation(INF_RULE, clause)));
    } else {
      return clause;
    }
  }

  struct TermTrans : public TermTransformer {
    QuotientEPreproc& _self;
    TermTrans(QuotientEPreproc& self) : _self(self) {}
    TermList transformSubterm(TermList t) override 
    { return _self.transformSubterm(t); }
  };

  FormulaUnit* proc(FormulaUnit* unit) 
  { 
    auto trans = TermTrans(*this);
    auto inf = Inference(FormulaClauseTransformation(INF_RULE, unit));
    return new FormulaUnit(TermTransformingFormulaTransformer(trans).transform(unit->formula()), inf); 
  }
  Unit* proc(Unit* unit) {
    return unit->isClause() 
      ? (Unit*)proc(static_cast<Clause*>(unit))
      : (Unit*)proc(static_cast<FormulaUnit*>(unit));
  }
public:

  void proc(Problem& prb)
  {
    for (auto& unit : iterTraits(prb.units()->iter())) {
      unit = proc(unit);
    }
    if (_addedITE) {
      prb.reportFOOLAdded();
    }
  }
};


} // namespace Kernel
 
#endif // __ALASCA_Preprocessor__

