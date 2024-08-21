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
 * @file UnificationWithAbstraction.cpp
 * Defines class AbstractionOracle.
 *
 */

#include "Debug/Output.hpp"
#include "Debug/Assertion.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Coproduct.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Recycled.hpp"
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/SortHelper.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/QKbo.hpp"
#include <functional>
#include "Debug/TimeProfiling.hpp"


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "Kernel/NumTraits.hpp"

#include "UnificationWithAbstraction.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Debug/Tracer.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)
#define DEBUG_FINALIZE(LVL, ...) if (LVL < 0) DBG(__VA_ARGS__)
#define DEBUG_UNIFY(LVL, ...) if (LVL < 0) DBG(__VA_ARGS__)


namespace Kernel
{

template<class NumTraits>
typename NumTraits::ConstantType divOrPanic(NumTraits n, typename NumTraits::ConstantType c1, typename NumTraits::ConstantType c2) { return c1 / c2; }
typename IntTraits::ConstantType divOrPanic(IntTraits n, typename IntTraits::ConstantType c1, typename IntTraits::ConstantType c2) { ASSERTION_VIOLATION }


template<class NumTraits>
AbstractionOracle::AbstractionResult lpar(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n, Options::UnificationWithAbstraction uwa);
Option<AbstractionOracle::AbstractionResult> lpar(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa);

bool uncanellableOccursCheck(AbstractingUnifier& au, VarSpec const& v, TermSpec const& t) {
  if (t.isSort()) return true; // <- for sorts arguments might never cancel out
  Recycled<Stack<TermSpec>> todo;
  ASS(t.isTerm())
  todo->push(t);
  while (!todo->isEmpty()) {
    auto t = todo->pop();
    auto& dt = au.subs().derefBound(t);
    if (dt.term.isTerm()) {
      auto f = dt.functor();
      auto argsMightCancel = forAnyNumTraits([&](auto n){
            // check if its subterms might cancel out
            return n.isAdd(f) || n.isMul(f);
         });
      if (!argsMightCancel) {
        todo->loadFromIterator(dt.termArgs());
      }
    } else if (dt.isVar() && v == dt.varSpec()) {
      return true;
    }
  }
  return false;
}

bool isAlascaInterpreted(unsigned f) {
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return numTraits.isAdd(f)
          || numTraits.isNumeral(f)
          || numTraits.isMinus(f)
          || numTraits.isMul(f);
  });
};

bool isAlascaInterpreted(TermSpec const& t, AbstractingUnifier& au) {
  if (t.isVar()) return false;
  ASS(!t.term.isTerm() || !t.term.term()->isLiteral()) 
  auto derefTerm = [&](auto i) { return au.subs().derefBound(t.termArg(0)); };
  auto f = t.functor();
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return numTraits.isAdd(f)
          || numTraits.isNumeral(f)
          || numTraits.isMinus(f)
          || (numTraits.isMul(f) && (
                 (derefTerm(0).isTerm() && numTraits.isNumeral(derefTerm(0).functor()))
              || (derefTerm(1).isTerm() && numTraits.isNumeral(derefTerm(1).functor()))
             ));
  });
};


template<class NumTraits, class Action>
auto iterAtoms(TermSpec outer, AbstractingUnifier& au, NumTraits n, Action action) {
  static TermSpec one = TermSpec(TermList(n.one()), 0);
  using Numeral = typename NumTraits::ConstantType;
  // auto action = [&](auto& term, auto numeral) {
  //   ASS(!isInterpreted(term))
  //   re
  // };

  Recycled<Stack<std::pair<TermSpec, Numeral>>> todo;
  todo->push(std::make_pair(std::move(outer), Numeral(1)));
  while (todo->isNonEmpty()) {
    auto pair = todo->pop();
    auto& term = au.subs().derefBound(pair.first);
    auto numeral = std::move(pair.second);
    if (numeral != Numeral(0)) {
      if (term.isVar()) {
        action(term, numeral);
      } else {
        auto f = term.functor();
        if (n.isMinus(f)) {
          todo->push(std::make_pair(term.termArg(0), -numeral));
          continue;

        } else if (n.isNumeral(f)) {
          action(one, numeral * (*n.tryNumeral(f)));
          continue;

        } else if (n.isMul(f)) {
          auto lhs_ = term.termArg(0);
          auto rhs_ = term.termArg(1);
          auto& lhs = au.subs().derefBound(lhs_);
          auto& rhs = au.subs().derefBound(rhs_);
          if (lhs.isTerm() && n.isNumeral(lhs.functor())) {
            todo->push(std::make_pair(rhs, numeral * (*n.tryNumeral(lhs.functor()))));

          } else if (rhs.isTerm() && n.isNumeral(rhs.functor())) {
            todo->push(std::make_pair(lhs, numeral * (*n.tryNumeral(rhs.functor()))));

          } else {
            // non-linear multiplication
            action(term, numeral);

          }
        } else if (n.isAdd(f)) {
          todo->push(std::make_pair(term.termArg(0), numeral));
          todo->push(std::make_pair(term.termArg(1), numeral));

        } else {
          // uninterpreted
          action(term, numeral);
        }
      }
    }

  }
};


Shell::Options::UnificationWithAbstraction AbstractionOracle::create()
{
  if (env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF) {
    return env.options->unificationWithAbstraction();
  } else if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.getMainProblem()->getProperty()->higherOrder()) { 
    return Options::UnificationWithAbstraction::FUNC_EXT;
  } else {
    return Options::UnificationWithAbstraction::OFF;
  }
}

Shell::Options::UnificationWithAbstraction AbstractionOracle::createOnlyHigherOrder()
{
  if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.getMainProblem()->getProperty()->higherOrder()) { 
    return Options::UnificationWithAbstraction::FUNC_EXT;
  } else {
    return Options::UnificationWithAbstraction::OFF;
  }
}

bool AbstractionOracle::isInterpreted(unsigned functor) const 
{
  auto f = env.signature->getFunction(functor);
  return f->interpreted() || f->termAlgebraCons();
}


class AcIter {
  unsigned _function;
  Recycled<Stack<TermSpec>> _todo;
  RobSubstitution const* _subs;
public:

  AcIter(unsigned function, TermSpec t, RobSubstitution const* subs) : _function(function), _todo(), _subs(subs) 
  { _todo->push(std::move(t)); }

  DECL_ELEMENT_TYPE(TermSpec);

  bool hasNext() const { return !_todo->isEmpty(); }

  TermSpec next() {
    ASS(!_todo->isEmpty());
    auto t = _todo->pop();
    auto* dt = &_subs->derefBound(t);
    while (dt->isTerm() && dt->functor() == _function) {
      ASS_EQ(dt->nTermArgs(), 2);
      _todo->push(dt->termArg(1));
      t = dt->termArg(0);
      dt = &_subs->derefBound(t);
    }
    return *dt;
  }
};



bool AbstractionOracle::canAbstract(AbstractingUnifier* au, TermSpec const& t1, TermSpec const& t2) const 
{
  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.isSort() || t2.isSort()) return false;

  // bool t1Interp = isInterpreted(t1.functor());
  // bool t2Interp = isInterpreted(t2.functor());
  bool bothNumbers = t1.isNumeral() && t2.isNumeral();

  switch(_mode) {
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      if(!(t1.isTerm() && t2.isTerm())) return false;
      return (isInterpreted(t1.functor()) && isInterpreted(t2.functor()) && !bothNumbers);
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      if(!(t1.isTerm() && t2.isTerm())) return false;
      return !bothNumbers && (isInterpreted(t1.functor()) || isInterpreted(t2.functor()));
    case Shell::Options::UnificationWithAbstraction::CONSTANT:
      if(!(t1.isTerm() && t2.isTerm())) return false;
      return !bothNumbers && (isInterpreted(t1.functor()) || isInterpreted(t2.functor()))
            && (isInterpreted(t1.functor()) || t1.nTermArgs())
            && (isInterpreted(t2.functor()) || t2.nTermArgs());
    case Shell::Options::UnificationWithAbstraction::ALL:
    case Shell::Options::UnificationWithAbstraction::GROUND:
      if(!(t1.isTerm() && t2.isTerm())) return false;
      return true;
    case Shell::Options::UnificationWithAbstraction::OFF:
      return false;
    case Shell::Options::UnificationWithAbstraction::AC1: 
    case Shell::Options::UnificationWithAbstraction::AC2: 
    case Shell::Options::UnificationWithAbstraction::LPAR_CAN_ABSTRACT: 
    case Shell::Options::UnificationWithAbstraction::LPAR_MAIN: 
    case Shell::Options::UnificationWithAbstraction::LPAR_ONE_INTERP: 
    case Shell::Options::UnificationWithAbstraction::FUNC_EXT: 
      ASSERTION_VIOLATION_REP(outputToString(_mode, " should be handled in AbstractionOracle::tryAbstract"))
  }
  ASSERTION_VIOLATION;
}

Option<AbstractionOracle::AbstractionResult> funcExt(
    AbstractingUnifier* au, 
    TermSpec const& t1, TermSpec const& t2)
{
  ASS(t1.isTerm() || t2.isTerm())

  auto isApp = [](auto& t) { return env.signature->isAppFun(t.functor()); };
  if ( (t1.isTerm() && t1.isSort()) 
    || (t2.isTerm() && t2.isSort()) ) return Option<AbstractionOracle::AbstractionResult>();
  if (t1.isTerm() && t2.isTerm()) {
    if (isApp(t1) && isApp(t2)) {
      auto argSort1 = au->subs().derefBound(t1.typeArg(0));
      auto argSort2 = au->subs().derefBound(t2.typeArg(0));
      if (t1.isVar() || t2.isVar()
       || argSort1.isVar() || argSort2.isVar()
       || env.signature->isArrowCon(argSort1.functor())
       || env.signature->isArrowCon(argSort2.functor())
       || env.signature->isBoolCon(argSort1.functor())
       || env.signature->isBoolCon(argSort2.functor())
       ) {
        auto& arg1 = au->subs().derefBound(t1.termArg(1));
        auto& arg2 = au->subs().derefBound(t2.termArg(1));
        auto out = AbstractionOracle::EqualIf()
              .unify (UnificationConstraint(t1.typeArg(0), t2.typeArg(0), TermSpec(AtomicSort::superSort(), 0)),
                      UnificationConstraint(t1.typeArg(1), t2.typeArg(1), TermSpec(AtomicSort::superSort(), 0)),
                      UnificationConstraint(t1.termArg(0), t2.termArg(0), t1.termArgSort(0)));

        auto argsEq = UnificationConstraint(arg1, arg2, t1.termArgSort(1));
        auto res = some(AbstractionOracle::AbstractionResult(
              // if both are variables we don't want to introduce a constraint
              arg1.isVar() && arg2.isVar()
                ? std::move(out).unify(std::move(argsEq))
                : std::move(out).constr(std::move(argsEq)))) ;
        return res;
      }
    }
  }
  return Option<AbstractionOracle::AbstractionResult>();
}

TermSpec norm(TermSpec outer, AbstractingUnifier& au) {

  auto& t = au.subs().derefBound(outer);
  if (t.isVar()) {
    return t;
  } else {
    auto s = t.sort();
    auto uninterpreted = [&](auto& orig){
      return orig.isVar() 
                ? orig
                : au.subs().createTermFromIter(orig.functor(), 
                    concatIters(
                      orig.typeArgs(),
                      orig.termArgs()
                      .map([&](TermSpec x) -> TermSpec {
                        // TODO unrecursify
                        return norm(x, au);
                        }))
                    );
    };
    auto cTerm = [&](auto... args) { return au.subs().createTerm(args...); };
    auto numResult = forAnyNumTraits([&](auto n){
        return someIf(s.term == n.sort(), [&](){
            using Numeral = typename decltype(n)::ConstantType;
            Recycled<Stack<std::pair<TermSpec, Numeral>>> sum;
            iterAtoms(t, au, n, [&](auto& term, auto num) {
                sum->push(std::make_pair(uninterpreted(term), num));
            });

            auto cmp = [&au](auto const& t1, auto const& t2) { 
              TIME_TRACE("comparing TermSpecs")
              auto top1 = t1.top();
              auto top2 = t2.top();
              auto v1 = !t1.isVar();
              auto v2 = !t2.isVar();
              if (std::tie(v1, top1) == std::tie(v2, top2)) {
                return TermSpec::compare(t1, t2, [&au](auto& t) -> decltype(auto) { return au.subs().derefBound(t); });
              } else {
                return std::tie(v1, top1) < std::tie(v2, top2) ? -1 : 1;
              }
            };

            auto sumUp = [](auto& diff, auto cmp) {
              unsigned i1 = 0;
              unsigned i2 = 1;
              while (i2 < diff.size()) {
                ASS(i1 < i2);
                auto c = cmp(diff[i1].first, diff[i2].first);
                ASS(c <= 0)
                if (c == 0) {
                  diff[i1].second += diff[i2].second;
                  i2++;
                } else {
                  ASS(c < 0)
                  if (diff[i1].second != Numeral(0)) {
                    // if there is a zero entry we override it
                    i1++;
                  }
                  if (i1 != i2) {
                    diff[i1] = std::move(diff[i2]);
                  }
                  i2++;
                }
              }
              if (diff[i1].second == Numeral(0)) 
                  diff.truncate(i1);
              else
                  diff.truncate(i1 + 1);
            };
            sum->sort([&](auto& l, auto& r) { return cmp(l.first, r.first) < 0; });
            sumUp(*sum, cmp);

            auto result = 
              arrayIter(*sum)
                .reverse()
                .map([&](auto& pair) { 
                    ASS(pair.second != Numeral(0))
                    auto k = pair.second;
                    auto& atomNorm = pair.first;

                    return k == Numeral( 1) ? std::move(atomNorm)
                         : k == Numeral(-1) ? cTerm(n.minusF(), std::move(atomNorm))
                         : cTerm(n.mulF(), cTerm(n.numeralF(k)), std::move(atomNorm));

                })
                .fold([&](auto l, auto r)
                    { return cTerm(n.addF(), std::move(l), std::move(r)); });
            return result.isSome() ? std::move(*result) : cTerm(n.numeralF(Numeral(0)));
        });

    });
    return numResult.isSome() ? std::move(*numResult) : uninterpreted(t);
  }
}

Option<AbstractionOracle::AbstractionResult> lpar(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa) {
  ASS(t1.isTerm() || t2.isTerm())

  auto interpreted = [&](TermSpec const& t) {
    if (t.isVar()) return false;
    ASS(!t.term.isTerm() || !t.term.term()->isLiteral()) 
    auto f = t.functor();
    return forAnyNumTraits([&](auto numTraits) -> bool {
        return numTraits.isAdd(f)
            || numTraits.isNumeral(f)
            || numTraits.isMinus(f)
            || (numTraits.isMul(f)
                && ((au.subs().derefBound(t.termArg(0)).isTerm() 
                     && numTraits.isNumeral(au.subs().derefBound(t.termArg(0)).functor()))
                ||( au.subs().derefBound(t.termArg(1)).isTerm() 
                     && numTraits.isNumeral(au.subs().derefBound(t.termArg(1)).functor()))
                ));
    });
  };


  if ((t1.isTerm() && t1.isSort()) 
  || ( t2.isTerm() && t2.isSort())) return {};

  auto i1 = interpreted(t1);
  auto i2 = interpreted(t2);

  auto occ = [&au](auto& v, auto& t) {
    ASS(v.isVar())
    ASS(t.isTerm())
    // we know due to the uwa algorithm that v occurs in t
    if (uncanellableOccursCheck(au, v.varSpec(), t)) {
      return some(AbstractionOracle::AbstractionResult(AbstractionOracle::NeverEqual{}));
    } else {
      // this means all
      return some(AbstractionOracle::AbstractionResult(AbstractionOracle::EqualIf().constr(UnificationConstraint(v, t, t.sort()))));
    }
  };

  if (i1 || i2) {
    using Mode = Options::UnificationWithAbstraction;
    auto sort = i1 ? t1.sort() : t2.sort();
    if (uwa == Mode::LPAR_ONE_INTERP) {
      return some(AbstractionOracle::AbstractionResult(AbstractionOracle::EqualIf()
          .constr(UnificationConstraint(t1, t2, sort))));
    }

    auto res = forAnyNumTraits([&](auto n) {
        return someIf(sort.term == n.sort(), [&]() { 
            return lpar(au, t1, t2, n, uwa); 
        });
    });
    ASS(res.isSome())
    if (uwa == Mode::LPAR_MAIN) {
      return res;
    } else {
      ASS(uwa == Mode::LPAR_CAN_ABSTRACT)
      if (res->template is<AbstractionOracle::EqualIf>())
        return  some(AbstractionOracle::AbstractionResult(AbstractionOracle::EqualIf()
            .constr(UnificationConstraint(t1, t2, t1.term.isTerm() ? t1.sort() : t2.sort()))));
      else return {};
    }
  } else {
    if (t1.isVar()) return occ(t1, t2);
    if (t2.isVar()) return occ(t2, t1);
    return {};
  }
}


template<class NumTraits>
AbstractionOracle::AbstractionResult lpar(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n, Options::UnificationWithAbstraction uwa) {
  TIME_TRACE("unification with abstraction ALASCA")
  using EqualIf = AbstractionOracle::EqualIf;
  using AbstractionResult = AbstractionOracle::AbstractionResult;
  using NeverEqual = AbstractionOracle::NeverEqual;
  using Numeral = typename NumTraits::ConstantType;

  
  auto cTerm = [&](auto... args) { return au.subs().createTerm(args...); };
  auto constraint = [&](auto lhs, auto rhs) { return UnificationConstraint(lhs, rhs, TermSpec(n.sort(), 0)); };

  Recycled<Stack<std::pair<TermSpec, Numeral>>> _diff;
  auto& diff = *_diff;
  auto dt = cTerm(n.addF(), cTerm(n.minusF(), t1), t2);
  auto nf = norm(std::move(dt), au);

  iterAtoms(std::move(nf), au, n,
    [&diff](auto& t, auto num) { diff.push(std::make_pair(t,  num)); });

  // TODO bin search if many elems
  auto nVars = range(0, diff.size())
    .find([&](auto i) { return !diff[i].first.isVar();  })
    .unwrapOrElse([&](){ return diff.size(); });


  ASS(nVars == 0 || diff[nVars - 1].first.isVar())
  ASS(nVars == diff.size() || !diff[nVars].first.isVar())


  auto numMul = [&cTerm](Numeral num, TermSpec t) {
    ASS(num != Numeral(0))
    if (num == Numeral(1)) {
      return std::move(t);

    } else if (num == Numeral(-1)) {
      return cTerm(NumTraits::minusF(), std::move(t));

    } else {
      return cTerm(NumTraits::mulF(), 
          cTerm(NumTraits::numeralF(num)),
          std::move(t)
      );
    }
  };

  auto sum = [&](auto iter) -> TermSpec {
      return iterTraits(std::move(iter))
        .map([&](auto x) { return numMul(x.second, std::move(x.first)); })
        .fold([&](auto l, auto r) 
          { return cTerm(NumTraits::addF(), std::move(l), std::move(r)); })
        .unwrapOrElse([&]() { return cTerm(NumTraits::numeralF(Numeral(0))); }); };

  // auto diffConstr = [&]() 
  // { return constraint(sum(diff1), sum(diff2)); };

  auto toConstr = [&](auto& stack) {
    return constraint(
              sum(arrayIter(stack)
                 .filter([](auto& x) { return x.second.isPositive(); })
                 .map([](auto& x) { return std::make_pair(std::move(std::move(x.first)), x.second); })),
              sum(arrayIter(stack)
                 .filter([](auto& x) { return !x.second.isPositive(); })
                 .map([](auto& x) { return std::make_pair(std::move(x.first), -x.second); })));
  };

  if (arrayIter(diff).any([&](auto& x) 
        { return x.first.isTerm() && n.isMul(x.first.functor()); })) {

    // non-linear multiplication. we cannot deal with this in alasca
    return AbstractionResult(EqualIf().constr(toConstr(diff)));

  } else if (diff.size() == 0) {
    return AbstractionResult(EqualIf());

  // } else if ( vars.hasNext() ) {



  } else if (nVars > 0) {
     Recycled<DHSet<TermSpec>> shieldedVars;
     for (auto i : range(nVars, diff.size())) {
       Recycled<Stack<TermSpec>> todo;
       todo->push(diff[i].first);
       while (todo->isNonEmpty()) {
         auto next_ = todo->pop();
         auto& next = au.subs().derefBound(next_);
         if (next.isVar()) {
           shieldedVars->insert(next);
         } else {
           todo->loadFromIterator(next.termArgs());
         }
       }
     }
     auto idx = 
       range(0, nVars)
          .find([&](auto i) 
                { return !shieldedVars->contains(diff[i].first); });

    if (idx) {
      // we have a variable unshielded in this unification
      auto num = diff[*idx].second;
      auto& var = diff[*idx].first;
      auto rest = [&]() 
      { return range(0, diff.size())
                .filter([&](auto i) { return i != *idx; })
                .map([&](auto i) { return std::move(diff[i]); }); };

      return AbstractionResult(ifIntTraits(n, 
            [&](auto n) { return num == Numeral(-1) ? EqualIf().unify(constraint(std::move(var), sum(rest())))
                               : num == Numeral( 1) ? EqualIf().unify(constraint(std::move(var), sum(rest().map([](auto x) { return std::make_pair(std::move(x.first), -std::move(x.second)); }))))
                               :                      EqualIf().constr(constraint(numMul(-num, std::move(var)), sum(rest())))
                                                    ; },
            // [&](auto n) { return EqualIf().unify(UnificationConstraint(numMul(-num, std::move(var)), sum(rest()))); },
            [&](auto n) { return EqualIf().unify(constraint(std::move(var), 
                sum(rest().map([&](auto x) { return std::make_pair(std::move(x.first), divOrPanic(n, x.second, -num)); })
                  ))); }
            ));

    } else {
      // all variables are shielded

      if (nVars == 1) {
       auto& var = diff[0].first;
       auto  num = diff[0].second;

       for (auto i : range(nVars, diff.size())) {
         if (uncanellableOccursCheck(au, var.varSpec(), diff[i].first)) {
           return AbstractionResult(NeverEqual{});
         }
       }
     }
     return AbstractionResult(EqualIf().constr(toConstr(diff)));
    }
  } 

  // no variables

  Recycled<Stack<UnificationConstraint>> unify;
  Recycled<Stack<UnificationConstraint>> constr;
  auto curF = diff[0].first.functor();
  Recycled<Stack<std::pair<TermSpec, Numeral>>> curPosSummands;
  Recycled<Stack<std::pair<TermSpec, Numeral>>> curNegSummands;
  auto curSum = Numeral(0);  


  auto curSumCanUnify = [&]() -> bool {
      if (curSum != Numeral(0)) {
        return false;

      } else if (curNegSummands->size() == 1) {
        for (auto& s : *curPosSummands) {
          unify->push(UnificationConstraint(
            (*curNegSummands)[0].first,
            std::move(s.first), 
            TermSpec(n.sort(), 0)));
        }
        return true;

      } else if (curPosSummands->size() == 1) {
        // ASS((*curPosSummands)[0].second == -(*curSummands)[1].second)
        for (auto& s : *curNegSummands) {
          unify->push(UnificationConstraint(
            (*curPosSummands)[0].first,
            std::move(s.first),
            TermSpec(n.sort(), 0)));
        }
        return true;

      } else {
        ASS(curPosSummands->size() + curNegSummands->size() >= 3)
        constr->push(UnificationConstraint(
              sum(arrayIter(*curPosSummands)
                 .map([](auto& x) { return std::make_pair(std::move(x.first), x.second); })),
              sum(arrayIter(*curNegSummands)
                 .map([](auto& x) { return std::make_pair(std::move(x.first), -x.second); })),
              TermSpec(n.sort(), 0)));
        return true;
      }
  };

  for (auto& x : diff) {
    auto f = au.subs().derefBound(x.first).functor();
    if (f != curF) {
      if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
      curF = f;
      curSum = Numeral(0);
      curPosSummands->reset();
      curNegSummands->reset();
    }
    curSum += x.second;
    (x.second.isPositive() ? curPosSummands : curNegSummands)->push(std::move(x));
  }
  if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
  return AbstractionResult(EqualIf().unify(std::move(unify)).constr(std::move(constr)));
}


Option<AbstractionOracle::AbstractionResult> AbstractionOracle::tryAbstract(AbstractingUnifier* au, TermSpec const& t1, TermSpec const& t2) const
{
  using Uwa = Shell::Options::UnificationWithAbstraction;
  ASS(_mode != Uwa::OFF)

  auto intSort = []() { return TermSpec(IntTraits::sort(), 0); };

  if (_mode == Uwa::AC1 || _mode == Uwa::AC2) {
      if ( (t1.isTerm() && t1.isSort())
        || (t2.isTerm() && t2.isSort())
        || !(t1.isTerm() && theory->isInterpretedFunction(t1.functor(), IntTraits::addI))
        || !(t2.isTerm() && theory->isInterpretedFunction(t2.functor(), IntTraits::addI))
        ) {
        return Option<AbstractionResult>();
      }
      auto a1 = iterTraits(AcIter(IntTraits::addF(), t1, &au->subs())).template collect<Stack>();
      auto a2 = iterTraits(AcIter(IntTraits::addF(), t2, &au->subs())).template collect<Stack>();
      auto cmp = [&](TermSpec const& lhs, TermSpec const& rhs) { return TermSpec::compare(lhs, rhs, [&](auto& t) -> TermSpec const& { return au->subs().derefBound(t); }); };
      auto less = [&](TermSpec const& lhs, TermSpec const& rhs) { return cmp(lhs, rhs) < 0; };
      a1.sort(less);
      a2.sort(less);

      Recycled<Stack<TermSpec>> diff1_;
      Recycled<Stack<TermSpec>> diff2_;
      auto& diff1 = *diff1_;
      auto& diff2 = *diff2_;
      diff1.loadFromIterator(iterSortedDiff(arrayIter(a1), arrayIter(a2), cmp));
      diff2.loadFromIterator(iterSortedDiff(arrayIter(a2), arrayIter(a1), cmp));
      auto sum = [&](auto& diff) {
          return arrayIter(diff)
            .map([](TermSpec& t) -> TermSpec { return t; })
            .fold([&](TermSpec l, TermSpec r) -> TermSpec
              { return au->subs().createTerm(IntTraits::addF(), l, r); })
            .unwrap(); };
      auto diffConstr = [&]() 
      { return UnificationConstraint(sum(diff1), sum(diff2), intSort()); };

      auto functors = [](auto& diff) 
      { return arrayIter(diff).map([](auto& f) { return f.functor(); }); };

      if (diff1.size() == 0 && diff2.size() == 0) {
        return some(AbstractionResult(EqualIf()));

      } else if (( diff1.size() == 0 && diff2.size() != 0 )
              || ( diff2.size() == 0 && diff1.size() != 0 ) ) {
        return some(AbstractionResult(NeverEqual{}));

      } else if (_mode == Uwa::AC2 && diff1.size() == 1 && diff1[0].isVar()) {
        return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff1[0]), sum(diff2), intSort()))));

      } else if (_mode == Uwa::AC2 && diff2.size() == 1 && diff2[0].isVar()) {
        return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff2[0]), sum(diff1), intSort()))));

      } else if (concatIters(arrayIter(diff1), arrayIter(diff2)).any([](auto& x) { return x.isVar(); })) {
        return some(AbstractionResult(EqualIf().constr(diffConstr())));

      } else if (iterSortedDiff(functors(diff1), functors(diff2)).hasNext()
              || iterSortedDiff(functors(diff2), functors(diff1)).hasNext()) {
        return some(AbstractionResult(NeverEqual{}));

      } else {
        return some(AbstractionResult(EqualIf().constr(diffConstr())));
      }

  } else if (_mode == Shell::Options::UnificationWithAbstraction::FUNC_EXT) {
    return funcExt(au, t1, t2);

  } else if (_mode == Shell::Options::UnificationWithAbstraction::LPAR_MAIN 
      || _mode == Shell::Options::UnificationWithAbstraction::LPAR_CAN_ABSTRACT 
      || _mode == Shell::Options::UnificationWithAbstraction::LPAR_ONE_INTERP
      ) {
    return lpar(*au, t1, t2, _mode);

  } else {
    auto abs = canAbstract(au, t1, t2);
    // DEBUG_UWA(1, "canAbstract(", t1, ",", t2, ") = ", abs);
    // DEBUG_UWA(1, "  ( ctx: ", *au, " )")
    return someIf(abs, [&](){
        return AbstractionResult(EqualIf().constr(UnificationConstraint(t1, t2, 
                t1.isTerm() ? TermSpec(SortHelper::getResultSort(t1.term.term()), t1.index)
                            : TermSpec(SortHelper::getResultSort(t2.term.term()), t2.index)
                )));
    });
  }
}

void UnificationConstraintStack::add(UnificationConstraint c, Option<BacktrackData&> bd)
{ 
  DEBUG("introduced constraint: ", c)
  _cont.push(c);
  if (bd) {
    bd->addClosure([this]() { _cont.pop(); });
  }
}


UnificationConstraint UnificationConstraintStack::pop(Option<BacktrackData&> bd)
{ 
  auto old = _cont.pop();
  if (bd) {
    bd->addClosure([this, old]() mutable { _cont.push(std::move(old)); });
  }
  return old;
}

Recycled<Stack<Literal*>> UnificationConstraintStack::literals(RobSubstitution& s)
{ 
  Recycled<Stack<Literal*>> out;
  out->reserve(_cont.size());
  out->loadFromIterator(literalIter(s));
  return out;
}


Option<Literal*> UnificationConstraint::toLiteral(RobSubstitution& s)
{ 
  auto t1 = _t1.toTerm(s);
  auto t2 = _t2.toTerm(s);
  auto sort = _sort.toTerm(s);
  return t1 == t2 
    ? Option<Literal*>()
    : Option<Literal*>(Literal::createEquality(false, t1, t2, sort));
}


}

bool AbstractingUnifier::fixedPointIteration()
{
  TIME_TRACE("uwa fixed point")
  Recycled<Stack<UnificationConstraint>> todo;
  while (!constr().isEmpty()) { 
    todo->push(constr().pop(bd()));
  }

  DEBUG_FINALIZE(1, "finalizing: ", todo)
  while (!todo->isEmpty()) {
    auto c = todo->pop();
    DEBUG_FINALIZE(2, "popped: ", c);
    bool progress;
    auto res = unify(c.lhs(), c.rhs(), progress);
    if (!res) {
      DEBUG_FINALIZE(1, "finalizing failed");
      return false;
    } else if (progress) {
      while (!constr().isEmpty()) { 
        todo->push(constr().pop(bd()));
      }
    } else {
      // no progress. we keep the constraints
    }
  }
  DEBUG_FINALIZE(1, "finalizing successful: ", *this);
  return true;
}

Option<Recycled<Stack<unsigned>>> AbstractingUnifier::unifiableSymbols(unsigned f)
{
  auto anything = []() -> Option<Recycled<Stack<unsigned>>> { return {}; };
  auto nothing  = []() -> Option<Recycled<Stack<unsigned>>> { return some(recycledStack<unsigned>()); };
  switch (_uwa._mode) {
    case Options::UnificationWithAbstraction::OFF: return some(recycledStack(f));
    case Options::UnificationWithAbstraction::INTERP_ONLY: return theory->isInterpretedFunction(f) ? anything() : some(recycledStack(f));
    case Options::UnificationWithAbstraction::ONE_INTERP: return anything();
    case Options::UnificationWithAbstraction::CONSTANT: return theory->isInterpretedConstant(f) ? anything() : nothing();
    case Options::UnificationWithAbstraction::ALL: return anything();
    case Options::UnificationWithAbstraction::GROUND: anything();
    case Options::UnificationWithAbstraction::FUNC_EXT: anything();
    case Options::UnificationWithAbstraction::AC1: return some(recycledStack(f));
    case Options::UnificationWithAbstraction::AC2: return some(recycledStack(f));
    case Options::UnificationWithAbstraction::LPAR_CAN_ABSTRACT: 
    case Options::UnificationWithAbstraction::LPAR_ONE_INTERP: 
    case Options::UnificationWithAbstraction::LPAR_MAIN: return isAlascaInterpreted(f) ? anything() : some(recycledStack(f));
  }
  ASSERTION_VIOLATION
}

bool AbstractingUnifier::unify(TermList term1, unsigned bank1, TermList term2, unsigned bank2)
{
  if (_uwa._mode == Shell::Options::UnificationWithAbstraction::OFF) 
    return _subs->unify(term1, bank1, term2, bank2);

  bool progress;
  return unify(TermSpec(term1, bank1), TermSpec(term2, bank2), progress);
}

bool AbstractingUnifier::unify(TermSpec t1, TermSpec t2, bool& progress)
{
  TIME_TRACE("unification with abstraction")
  ASS_NEQ(_uwa._mode, Shell::Options::UnificationWithAbstraction::OFF) 
  DEBUG_UNIFY(0, *this, ".unify(", t1, ",", t2, ")")
  progress = false;

  if(t1 == t2) {
    progress = true;
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<std::pair<TermSpec, TermSpec>>> toDo;
    toDo->push(std::make_pair(t1, t2));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<std::pair<TermSpec,TermSpec>>> encountered;

    Option<AbstractionOracle::AbstractionResult> absRes;
    auto doAbstract = [&](auto& l, auto& r) -> bool
    { 
      if (absRes.isSome()) DEBUG_UNIFY(1, "uwa: ", absRes)
      absRes = _uwa.tryAbstract(this, l, r);
      if (absRes) {
        DEBUG_UNIFY(1, "abstraction result: ", absRes)
      }
      return absRes.isSome();
    };

    auto pushTodo = [&](auto pair) {
        // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
        // in order to safe memory we do ot do this for variables.
        // (Note by joe:  didn't make this decision, but just keeping the implemenntation 
        // working as before. i.e. as described in the paper "Comparing Unification 
        // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
        // TODO restore this branch?
        // if (std::pair.first.isVar() && isUnbound(std::pair.first.varSpec()) &&
        //     pair.second.isVar() && isUnbound(std::pair.second.varSpec())) {
        //   todo.push(std::pair);
        // } else 
        if (!encountered->find(pair)) {
          encountered->insert(pair);
          toDo->push(std::move(pair));
        }
    };

    auto occurs = [this](auto& var, auto& term) {
      Recycled<Stack<TermSpec>> todo;
      todo->push(term);
      while (todo->isNonEmpty()) {
        auto t = todo->pop();
        auto& dt = subs().derefBound(t);
        if (dt.isVar()) {
          if (dt == var) {
            return true;
          }
        } else {
          todo->loadFromIterator(dt.allArgs());
        }
      }
      return false;
    };


    while (toDo->isNonEmpty()) {
      auto cur = toDo->pop();
      DEBUG_UNIFY(1, "popped: ", cur)
      auto& dt1 = subs().derefBound(cur.first);
      auto& dt2 = subs().derefBound(cur.second);
      DEBUG_UNIFY(1, "dereferenced: ", dt1, " ?= ", dt2)
      if (dt1.deepEqCheck(dt2)) {
        progress = true;

      } else if(dt1.isVar() && !occurs(dt1, dt2)) {
        progress = true;
        DEBUG_UNIFY(2, "binding: ", dt1, " -> ", dt2)
        subs().bind(dt1.varSpec(), dt2);

      } else if(dt2.isVar() && !occurs(dt2, dt1)) {
        progress = true;
        DEBUG_UNIFY(2, "binding: ", dt2, " -> ", dt1)
        subs().bind(dt2.varSpec(), dt1);

      } else if(doAbstract(dt1, dt2)) {

        ASS(absRes);
        if (absRes->is<AbstractionOracle::NeverEqual>()) {
          return false;

        } else {
          ASS(absRes->is<AbstractionOracle::EqualIf>())
          auto& conditions = absRes->unwrap<AbstractionOracle::EqualIf>();
          auto deepEqCheck = [](UnificationConstraint& c, TermSpec const& lhs, TermSpec const& rhs) 
          { 
            return (c.lhs().deepEqCheck(lhs) && c.rhs().deepEqCheck(rhs)) 
                || (c.lhs().deepEqCheck(rhs) && c.rhs().deepEqCheck(lhs)); };
          if (progress 
              || conditions.constr().size() != 1 
              || conditions.unify().size() != 0
              || !deepEqCheck(conditions.constr()[0], t1, t2)
              ) {
            progress = true;
          }
          for (auto& x : conditions.unify()) {
            auto pair = std::make_pair(x.lhs(), x.rhs());
            ASS_NEQ(pair, cur)
            pushTodo(pair);
            DEBUG_UNIFY(2, "uwa adding unify : ", pair)
          }
          for (auto& x: conditions.constr()) {
            _constr->add(std::move(x), bd());
            DEBUG_UNIFY(2, "uwa adding constr: ", x)
          }
        }
        absRes.take();

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        for (auto p : dt1.allArgs().zip(dt2.allArgs())) {
          pushTodo(p);
        }

      } else {
        return false;
      }

    }
    return true;
  };

  BacktrackData localBD;
  bdRecord(localBD);
  bool success = impl();
  bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(subs().bdIsRecording()) {
      subs().bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(0, *this, " (", success ? "success" : "fail", ")")
  return success;
}




