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
 * Defines functions and structres that are shared by all ALASCA inference rules in order to select literals, terms, etc.
 */

#ifndef __ALASCA_Preprocessor__
#define __ALASCA_Preprocessor__

#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Theory.hpp"

#define DEBUG_TRANSLATION(...) // DBG(__VA_ARGS__)

namespace Kernel {

class AlascaPreprocessor 
{
  Map<unsigned, unsigned> _preds;
  Map<unsigned, unsigned> _funcs;
  // all the functions func_R where func is an integer function
  Set<unsigned> _intFuncThatWasTransformedToRealFunc;

  using Z = IntTraits;
  using R = RealTraits;
  static constexpr InferenceRule INF_RULE = InferenceRule::ALASCA_INTEGER_TRANSFORMATION;

  Literal* integerConversion(Literal* l)
  {
    auto lit = InequalityNormalizer::normalize(l).toLiteral();
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
          if (t.isVar()) {
            return t.sort() == IntTraits::sort() ?  RealTraits::floor(t) : t;
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

              } else if (Z::isQuotientF(f) || R::isQuotientF(f)) {
                return quotF(args[0], args[1]);

              } else if (R::isToInt(f)) {
                return TermList(RealTraits::floor(args[0]));

              } else {
                auto out = TermList(Term::create(this->integerFunctionConversion(f), t.term()->arity(), args));
                return out;
              }
            }
          }
      })
      .context(Lib::TermListContext{ .ignoreTypeArgs = false, })
      .apply(t);
  }

#define TRANSLATE_ARRAY(PredicateOrFunction, fnPredType, itp)                             \
  {                                                                                       \
        if (theory->isInterpreted ## PredicateOrFunction(f, itp)) {                       \
          auto sym = env.signature->get ## PredicateOrFunction(f);                        \
          auto arraySort = theory->getArraySort(sym->fnPredType(), itp);                  \
          ASS(arraySort.isTerm())                                                         \
          ASS(env.signature->isArrayCon(arraySort.term()->functor()))                     \
          auto newArraySort = integerConversion(TypedTermList(arraySort, AtomicSort::superSort())); \
          return env.signature->addInterpreted ## PredicateOrFunction(itp, theory->getArrayOperatorType(newArraySort, itp), sym->name()); \
        }                                                                                 \
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

      TRANSLATE_ARRAY(Predicate, predType, Theory::ARRAY_BOOL_SELECT)

      auto sym = env.signature->getPredicate(f);
      auto ty = sym->predType();
      auto sorts_changed = false;
      auto intConv= [&](auto x) { 
        auto out = integerConversion(TypedTermList(x, AtomicSort::superSort())); 
        sorts_changed |= out != x;
        return out;
      };
      Recycled<Stack<TermList>> arg_sorts;
      for (auto i : range(0, ty->numTermArguments())) {
        arg_sorts->push(intConv(ty->termArg(i)));
      }

      if (sorts_changed) {
        auto name = sym->name() + "_R";
        unsigned nf = env.signature->addFreshPredicate2(sym->arity(), name.c_str());

        auto nsym = env.signature->getPredicate(nf);
        auto nty = OperatorType::getPredicateType(arg_sorts->size(), arg_sorts->begin(), ty->numTypeArguments());
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
      ASS_NOT(Theory::INT_CEILING)
      ASS_NOT(Theory::INT_TRUNCATE)
      ASS_NOT(Theory::INT_ROUND)
      ASS_NOT(Theory::INT_ABS)
#undef ASS_NOT

      TRANSLATE_ARRAY(Function, fnType, Theory::ARRAY_SELECT)
      TRANSLATE_ARRAY(Function, fnType, Theory::ARRAY_STORE)

      auto sorts_changed = false;
      auto sym = env.signature->getFunction(f);
      auto ty = sym->fnType();

      auto intConv= [&](auto x) { 
        auto out = integerConversion(TypedTermList(x, AtomicSort::superSort())); 
        sorts_changed |= out != x;
        return out;
      };
      Recycled<Stack<TermList>> sorts;
      for (auto i : range(0, ty->numTermArguments())) {
        sorts->push(intConv(ty->termArg(i)));
      }
      auto res_sort = intConv(ty->result());
      if (sorts_changed) {
        auto name = sym->name() + "_R";
        unsigned nf = env.signature->addFreshFunction2(sym->arity(), name.c_str());
        _intFuncThatWasTransformedToRealFunc.insert(nf);
        auto nsym = env.signature->getFunction(nf);
        auto nty = OperatorType::getFunctionType(sorts->size(), sorts->begin(), res_sort, ty->numTypeArguments());
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

  bool isIntValued(Term* t) const { 
   if (auto q = R::tryNumeral(t)) {
      if (q->isInt()) {
        return true;
      } else {
        return false;
      }
    } else {
      return R::isFloor(t) || _intFuncThatWasTransformedToRealFunc.contains(t->functor());
    }
  }

  bool isIntValued(TermList t) const { return t.isTerm() && isIntValued(t.term()); }

  Clause* integerConversion(Clause* clause)
  {
    auto notInt = [&](auto t) -> Option<Literal*> { 
      if (isIntValued(t)) {
        return {};
      }
      return some(R::eq(false, t, R::floor(t))); 
    };
    auto change = false;
    Recycled<Stack<Literal*>> res;
    for (auto l_ : clause->iterLits()) {
      auto l = InequalityNormalizer::normalize(l_).toLiteral();
      auto ll = integerConversion(l);
      change |= ll != l;
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


  AlascaPreprocessor() 
    : _preds()
    , _funcs() {}

  void integerConversion(Problem& prb)
  {
    for (auto& unit : iterTraits(prb.units()->iter())) {
      unit = integerConversion(unit);
    }
    // if (!_useFloor) {
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
            auto cl = Clause::fromLiterals({ R::eq(true, R::floor(t), t) }, inf);
            UnitList::push(cl, prb.units());
          }
        }
      }
    // }
    
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

    auto lit = [](auto c) { return new AtomicFormula(c); };
    auto conj = [](auto... cs) { return new JunctionFormula(Connective::AND, FormulaList::fromIterator(iterItems<Formula*>(cs...))); };
    auto iff = [](auto l, auto r) { return new BinaryFormula(Connective::IFF, l, r); };
    auto neg = [](auto f) { return new NegatedFormula(f); };

    auto ite = [this](auto c, auto x, auto y) 
    { 
      _addedITE = true;
      return TermList(Term::createITE(c, x, y, Z::sort())); };

    auto eq = [&](auto l, auto r) { return lit(Z::eq(true, l, r)); };
    auto gt = [&](auto l, auto r) { return lit(Z::greater(true, l, r)); };

    auto quotientF = [&](auto a, auto b) {
      return Z::quotientF(a, b);
    };    

    auto quotientE = [&](auto a, auto b) {
      return ite(gt(b, Z::zero()), 
              /* if ( (a > 0) == (b > 0) ) ==>  quotientF( a,b) */          Z::quotientF(a, b),
              /* else                          -quotientF(-a,b) */ Z::minus(Z::quotientF(Z::minus(a), b)));
    };    

    auto quotientT = [&](auto a, auto b) {
      return ite(iff(gt(a, Z::zero()), gt(b, Z::zero())), 
               /* if ( (a > 0) == (b > 0) ) ==>  quotientF( a,b) */ Z::quotientF(a, b),
               /* else                      ==> -quotientF(-a,b) */ Z::minus(Z::quotientF(Z::minus(a), b))
      );
    };

    auto rem = [&](auto quot) {
      // quot(a,b) * b + rem(a,b) = a
      // rem(a,b) = a - quot(a,b) * b
      return [=](auto a, auto b) {
        return Z::add(a, Z::minus(Z::mul(b, quot(a,b))));
      };
    };

    auto transQR = [&](auto quot, auto origF, auto a, auto b) {
      return ite(eq(b, Z::zero()), origF(a, Z::zero())
                                 , quot(a,b));
    };

    if (Z::isQuotientE(t) && trm.termArg(1) != Z::zero()) {
      return transQR(quotientE, Z::quotientE, trm.termArg(0), trm.termArg(1));

    } else if (Z::isRemainderE(t)) {
      return transQR(rem(quotientE), Z::remainderE, trm.termArg(0), trm.termArg(1));

    } else if (Z::isQuotientT(t) && trm.termArg(1) != Z::zero()) {
      return transQR(quotientT, Z::quotientT, trm.termArg(0), trm.termArg(1));

    } else if (Z::isRemainderT(t)) {
      return transQR(rem(quotientT), Z::remainderT, trm.termArg(0), trm.termArg(1));


    } else if (Z::isRemainderF(t)) {
      return transQR(rem(quotientF), Z::remainderF, trm.termArg(0), trm.termArg(1));
    }

    auto numRes = forAnyNumTraits([&](auto n) -> Option<TermList> {

      if (n.isTruncate(t)) {
        auto arg = t.term()->termArg(0);
        return some(ite(lit(n.geq(true, arg, n.zero())),
              n.floor(arg),
              n.minus(n.floor(n.minus(arg)))
        ));
      } else {

      if (n.isCeiling(t)) {
        return some(n.minus(n.floor(n.minus(t.term()->termArg(0)))));
      } else {

        return {};
      }

    });
    if (numRes) return *numRes;
    return t;
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
    virtual TermList transformSubterm(TermList t) override 
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

