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

#include "Lib/Output.hpp"
#include "Debug/Assertion.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Recycled.hpp"
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/SortHelper.hpp"
#include "Debug/TimeProfiling.hpp"


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "Kernel/NumTraits.hpp"

#include "UnificationWithAbstraction.hpp"
#include "Kernel/SortHelper.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#define DEBUG_FINALIZE(LVL, ...) if (LVL < 0) DBG(__VA_ARGS__)
#define DEBUG_UNIFY(LVL, ...) if (LVL < 0) DBG(__VA_ARGS__)

template<class T>
auto tuple_flatten(T t) 
{ return apply([](auto... args) { return std::tuple_cat(args...); }, t); }

namespace Kernel
{

template<class NumTraits>
typename NumTraits::ConstantType divOrPanic(NumTraits n, typename NumTraits::ConstantType c1, typename NumTraits::ConstantType c2) { return c1 / c2; }
typename IntTraits::ConstantType divOrPanic(AlascaSignature<IntTraits> n, typename IntTraits::ConstantType c1, typename IntTraits::ConstantType c2) { ASSERTION_VIOLATION }
typename IntTraits::ConstantType divOrPanic(IntTraits n, typename IntTraits::ConstantType c1, typename IntTraits::ConstantType c2) { ASSERTION_VIOLATION }


template<class NumTraits>
AbstractionOracle::AbstractionResult alasca(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n, Options::UnificationWithAbstraction uwa);
Option<AbstractionOracle::AbstractionResult> alasca(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa);

template<class NumTraits>
AbstractionOracle::AbstractionResult uwa_floor(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n, Options::UnificationWithAbstraction uwa);
Option<AbstractionOracle::AbstractionResult> uwa_floor(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa);

AbstractionOracle::AbstractionResult uwa_floor(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, IntTraits n, Options::UnificationWithAbstraction uwa) {
  // TODO use uwa_floor
  // TODO remove uwa arg
  return alasca(au, t1, t2, n, uwa);
}

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
            return n.isAdd(f);
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
          || numTraits.isLinMul(f);
  });
};

// TODO get rid of minus in alasca
bool isAlascaiInterpreted(unsigned f) {
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return numTraits.isAdd(f)
          || numTraits.isLinMul(f)
          || numTraits.isFloor(f);
  });
};

bool isAlascaInterpreted(TermSpec const& t, AbstractingUnifier& au) {
  if (t.isVar()) return false;
  ASS(!t.term.isTerm() || !t.term.term()->isLiteral()) 
  auto f = t.functor();
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return numTraits.isAdd(f)
          || numTraits.isLinMul(f);
  });
};


template<class ASig, class Action>
auto iterAtoms(TermSpec outer, AbstractingUnifier& au, ASig sig, Action action) {
  using Numeral = typename ASig::ConstantType;

  Recycled<Stack<std::pair<TermSpec, Numeral>>> todo;
  todo->push(std::make_pair(std::move(outer), Numeral(1)));
  while (todo->isNonEmpty()) {
    auto pair = todo->pop();
    auto& term = au.subs().derefBound(pair.first);
    auto numeral = std::move(pair.second);
    if (numeral != 0) {
      if (term.isVar()) {
        action(term, numeral);
      } else {
        auto f = term.functor();
        if (auto c = sig.tryLinMul(f)) {
          auto rhs_ = term.termArg(0);
          auto& rhs = au.subs().derefBound(rhs_);
          todo->push(std::make_pair(rhs, numeral * (*c)));

        } else if (auto c = sig.tryNumeral(term.term)) {
          action(TermSpec(sig.one(), 0), numeral * (*c));

        } else if (sig.isAdd(f)) {
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
    case Shell::Options::UnificationWithAbstraction::ALASCA_CAN_ABSTRACT:
    case Shell::Options::UnificationWithAbstraction::ALASCA_MAIN:
    case Shell::Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR:
    case Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP:
    case Shell::Options::UnificationWithAbstraction::FUNC_EXT:
      ASSERTION_VIOLATION_REP(Output::cat(_mode, " should be handled in AbstractionOracle::tryAbstract"))
    case Shell::Options::UnificationWithAbstraction::AUTO:
      ASSERTION_VIOLATION_REP("UnificationWithAbstraction::AUTO should have been resolved to a concrete value by now")
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
        auto arg1 = au->subs().derefBound(t1.termArg(1));
        auto arg2 = au->subs().derefBound(t2.termArg(1));
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
    auto numResult = forAnyNumTraits([&](auto n_){
        using ASig = AlascaSignature<decltype(n_)>;
        return someIf(s.term == ASig::sort(), [&](){
            using Numeral = typename ASig::ConstantType;
            Recycled<Stack<std::pair<TermSpec, Numeral>>> sum;
            iterAtoms(t, au, ASig{}, [&](auto term, auto num) {
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
              if (diff.size() == 0) return;
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
                  if (diff[i1].second != 0) {
                    // if there is a zero entry we override it
                    i1++;
                  }
                  if (i1 != i2) {
                    diff[i1] = std::move(diff[i2]);
                  }
                  i2++;
                }
              }
              if (diff[i1].second == 0) 
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
                    ASS(pair.second != 0)
                    auto k = pair.second;
                    auto& atomNorm = pair.first;

                    return k == 1 ? std::move(atomNorm)
                                  : cTerm(ASig::linMulF(k), std::move(atomNorm));

                })
                .fold([&](auto l, auto r)
                    { return cTerm(ASig::addF(), std::move(l), std::move(r)); });
            return result.isSome() ? std::move(*result) : TermSpec(ASig::numeralTl(0), 0);
        });

    });
    return numResult.isSome() ? std::move(*numResult) : uninterpreted(t);
  }
}

Option<AbstractionOracle::AbstractionResult> uwa_floor(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa) {
  ASS(t1.isTerm() || t2.isTerm())

  auto interpreted = [&](TermSpec const& t) {
    if (t.isVar()) return false;
    ASS(!t.term.isTerm() || !t.term.term()->isLiteral()) 
    auto f = t.functor();
    return forAnyNumTraits([&](auto n) -> bool {
        using ASig = AlascaSignature<decltype(n)>;
        return ASig::isAdd(f)
            || ASig::isOne(f)
            || ASig::isNumeral(t.term)
            || ASig::isFloor(f)
            || ASig::isLinMul(f);
    });
  };


  if ((t1.isTerm() && t1.isSort()) 
  || ( t2.isTerm() && t2.isSort())) return {};

  auto i1 = interpreted(t1);
  auto i2 = interpreted(t2);

  // TODO do we want/need this?
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
    if (uwa == Mode::ALASCA_ONE_INTERP) {
      return some(AbstractionOracle::AbstractionResult(AbstractionOracle::EqualIf()
          .constr(UnificationConstraint(t1, t2, sort))));
    }

    auto res = forAnyNumTraits([&](auto n) {
        return someIf(sort.term == n.sort(), [&]() { 
            return uwa_floor(au, t1, t2, n, uwa); 
        });
    });
    ASS(res.isSome())
    ASS_EQ(uwa, Mode::ALASCA_MAIN_FLOOR);
    return res;
  } else {
    if (t1.isVar()) return occ(t1, t2);
    if (t2.isVar()) return occ(t2, t1);
    return {};
  }
}

// TODO rename
Option<AbstractionOracle::AbstractionResult> alasca(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, Options::UnificationWithAbstraction uwa) {
  ASS(t1.isTerm() || t2.isTerm())

  auto interpreted = [&](TermSpec const& t) {
    if (t.isVar()) return false;
    ASS(!t.term.isTerm() || !t.term.term()->isLiteral()) 
    auto f = t.functor();
    return forAnyNumTraits([&](auto n) -> bool {
        using ASig = AlascaSignature<decltype(n)>;
        return ASig::isAdd(f)
            || ASig::isOne(f)
            || ASig::isLinMul(f);
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
    if (uwa == Mode::ALASCA_ONE_INTERP) {
      return some(AbstractionOracle::AbstractionResult(AbstractionOracle::EqualIf()
          .constr(UnificationConstraint(t1, t2, sort))));
    }

    auto res = forAnyNumTraits([&](auto n) {
        return someIf(sort.term == n.sort(), [&]() { 
            return alasca(au, t1, t2, n, uwa); 
        });
    });
    ASS(res.isSome())
    if (uwa == Mode::ALASCA_MAIN) {
      return res;
    } else {
      ASS(uwa == Mode::ALASCA_CAN_ABSTRACT)
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
AbstractionOracle::AbstractionResult alasca(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n_, Options::UnificationWithAbstraction uwa) {
  TIME_TRACE("unification with abstraction ALASCA")
  AlascaSignature<NumTraits> sig;
  Option<UnificationConstraint> sortsUnif;
  auto equalIf = [&]() {
    if (sortsUnif.isSome()) {
      return AbstractionOracle::EqualIf()
                     .unify(*sortsUnif.take());
    } else {
      return AbstractionOracle::EqualIf();
    }
  };
  using AbstractionResult = AbstractionOracle::AbstractionResult;
  using NeverEqual = AbstractionOracle::NeverEqual;
  using Numeral = typename NumTraits::ConstantType;
  
  auto cTerm = [&](auto... args) { return au.subs().createTerm(args...); };
  auto constraint = [&](auto lhs, auto rhs) { return UnificationConstraint(lhs, rhs, TermSpec(sig.sort(), 0)); };

#define CHECK_SORTS(t1, t2)                                                               \
  if (t1.isTerm()) {                                                                      \
    auto s1 = au.subs().derefBound(t1.sort());                                            \
    if (s1.isVar()) {                                                                     \
      ASS(sortsUnif.isNone())                                                             \
      sortsUnif = some(UnificationConstraint(s1, TermSpec(sig.sort(), 0), TermSpec(AtomicSort::superSort(), 0))); \
    } else if (s1.term != sig.sort()) {                                                   \
      return AbstractionResult(NeverEqual{});                                             \
    }                                                                                     \
  }                                                                                       \

  CHECK_SORTS(t1, t2)
  CHECK_SORTS(t2, t1)

  Recycled<Stack<std::pair<TermSpec, Numeral>>> _diff;
  auto& diff = *_diff;
  // TODO prevent these cterm calls?
  auto dt = cTerm(sig.addF(), cTerm(sig.minusF(), t1), t2);
  auto nf = norm(std::move(dt), au);

  iterAtoms(std::move(nf), au, sig,
    [&diff](auto t, auto num) { diff.push(std::make_pair(t,  num)); });

  // TODO bin search if many elems
  auto nVars = range(0, diff.size())
    .find([&](auto i) { return !diff[i].first.isVar();  })
    .unwrapOrElse([&](){ return diff.size(); });

  ASS(nVars == 0 || diff[nVars - 1].first.isVar())
  ASS(nVars == diff.size() || !diff[nVars].first.isVar())

  auto sum = [&](auto iter) -> TermSpec {
      return iterTraits(std::move(iter))
        .map([&](auto x) { return numMul(x.second, std::move(x.first)); })
        .fold([&](auto l, auto r) 
          { return cTerm(sig.addF(), std::move(l), std::move(r)); })
        .unwrapOrElse([&]() { return TermSpec(sig.numeralTl(Numeral(0)), 0); }); };

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
        { return x.first.isTerm() && NumTraits::isMul(x.first.functor()); })) {

    // non-linear multiplication. we cannot deal with this in alasca
    return AbstractionResult(equalIf().constr(toConstr(diff)));

  } else if (diff.size() == 0) {
    return AbstractionResult(equalIf());

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

      return AbstractionResult(ifIntTraits(NumTraits{}, 
            // TODO
            [&](auto n) { return num == -1 ? equalIf().unify(constraint(std::move(var), sum(rest())))
                               : num ==  1 ? equalIf().unify(constraint(std::move(var), sum(rest().map([](auto x) { return std::make_pair(std::move(x.first), -std::move(x.second)); }))))
                               :                      equalIf().constr(constraint(numMul(-num, std::move(var)), sum(rest())))
                                                    ; },
            [&](auto n) { return equalIf().unify(constraint(std::move(var), 
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
     return AbstractionResult(equalIf().constr(toConstr(diff)));
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
            TermSpec(sig.sort(), 0)));
        }
        return true;

      } else if (curPosSummands->size() == 1) {
        for (auto& s : *curNegSummands) {
          unify->push(UnificationConstraint(
            (*curPosSummands)[0].first,
            std::move(s.first),
            TermSpec(sig.sort(), 0)));
        }
        return true;

      } else {
        ASS(curPosSummands->size() + curNegSummands->size() >= 3)
        constr->push(UnificationConstraint(
              sum(arrayIter(*curPosSummands)
                 .map([](auto& x) { return std::make_pair(std::move(x.first), x.second); })),
              sum(arrayIter(*curNegSummands)
                 .map([](auto& x) { return std::make_pair(std::move(x.first), -x.second); })),
              TermSpec(sig.sort(), 0)));
        return true;
      }
  };

  for (auto& x : diff) {
    auto f = au.subs().derefBound(x.first).functor();
    if (f != curF) {
      if (!curSumCanUnify()) { return AbstractionResult(NeverEqual{});}
      curF = f;
      curSum = Numeral(0);
      curPosSummands->reset();
      curNegSummands->reset();
    }
    curSum += x.second;
    (x.second.isPositive() ? curPosSummands : curNegSummands)->push(std::move(x));
  }
  if (!curSumCanUnify()) { return AbstractionResult(NeverEqual{});}
  return AbstractionResult(equalIf().unify(std::move(unify)).constr(std::move(constr)));
}


template<class ASig>
struct FloorUwaState {
  using Numeral = typename ASig::Numeral;
  using Monom = std::pair<TermSpec, Numeral>;
  RStack<Monom> ratVars;
  RStack<Monom> intVars;
  RStack<Monom> mixVars;
  RStack<Monom> ratAtoms;
  RStack<Monom> intAtoms;
  Recycled<DHSet<VarSpec>> ratVarSet;
  Recycled<DHSet<VarSpec>> mixVarSet;
  Recycled<DHSet<VarSpec>> intVarSet;
  Recycled<DHSet<VarSpec>> shieldedVars;

  bool isShielded(TermSpec t) const { return shieldedVars->find(t.varSpec()); }
  bool isMixVar(VarSpec v) const { return mixVarSet->find(v) || (intVarSet->find(v) && ratVarSet->find(v)); }
  bool isMixVar(TermSpec t) const { return isMixVar(t.varSpec()); }

  friend std::ostream& operator<<(std::ostream& out, FloorUwaState const& self)
  { return out << Output::interleaved(" + ", self.summands()); }

  unsigned size() const 
  { return ratVars->size() + intVars->size() + mixVars->size() + ratAtoms->size() + intAtoms->size(); }

  static FloorUwaState zero() {
    return FloorUwaState();
  }

  static FloorUwaState one(AbstractingUnifier& au) {
    auto s = FloorUwaState();
    s.intAtoms->push(std::make_pair(TermSpec(ASig::one(), 0), Numeral(1)));
    return s;
  }

  static FloorUwaState add(AbstractingUnifier& au, FloorUwaState s1, FloorUwaState s2) {
    auto mergeArray = [](auto& l, auto& r) {
      auto compare = [](auto& l, auto& r) { return TermSpec::compare(l.first, r.first,
          [](auto& t) -> auto& { return t; }); };
      //  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      // TODO create option for "deep" compare using a different deref clsoure
      l.sort([&](auto& l, auto& r) { return compare(l, r) < 0; });
      r.sort([&](auto& l, auto& r) { return compare(l, r) < 0; });
      size_t li = 0;
      size_t ri = 0;
      size_t lEnd = l.size();
      size_t rEnd = r.size();
      while (li < lEnd && ri < rEnd) {
        auto cmp = compare(l[li], r[ri]);
        if (cmp == 0) {
          l[li].second += r[ri].second;
          ri++;
        } else if (cmp > 0) {
          l.push(r[ri++]);
        } else {
          li++;
        }
      }
      if (li == lEnd) {
        while (ri < rEnd) {
          l.push(r[ri++]);
        }
      }
      size_t read = 0;
      size_t write = 0;
      while (read < l.size()) {
        if (l[read].second == 0) {
          read++;
        } else {
          l[write++] = l[read++];
        }
      }
      l.pop(l.size() - write);
    };
    mergeArray(*s1.ratVars, *s2.ratVars);
    mergeArray(*s1.intVars, *s2.intVars);
    mergeArray(*s1.mixVars, *s2.mixVars);
    mergeArray(*s1.ratAtoms, *s2.ratAtoms);
    mergeArray(*s1.intAtoms, *s2.intAtoms);
    auto mergeSet = [](auto& l, auto& r) { l.loadFromIterator(r.iterator()); };
    mergeSet(*s1.ratVarSet, *s2.ratVarSet);
    mergeSet(*s1.mixVarSet, *s2.mixVarSet);
    mergeSet(*s1.intVarSet, *s2.intVarSet);
    mergeSet(*s1.shieldedVars, *s2.shieldedVars);
    return s1;
  }
  static FloorUwaState floor(AbstractingUnifier& au, FloorUwaState s) {
    auto out = FloorUwaState();
    /* out.ratAtoms none */
    /* out.ratVars  none */
    /* out.intVars empty */
    /* out.ratVarSet */
    out.mixVarSet = std::move(s.mixVarSet);
    /* out.intVarSet empty */
    out.shieldedVars = std::move(s.shieldedVars);

    auto push = [](auto& stack, auto a, auto num) { if (num != 0) stack->push(std::make_pair(a, num)); };
    auto insertVar = [](auto& set, auto v, auto num) { if (num != 0) set->insert(v.varSpec()); };

    RStack<Monom> floorIntVars;
    for (auto [a, k] : arrayIter(*s.intVars)) {
      push(out.intVars, a, Numeral(k.floor()));
      insertVar(out.intVarSet, a.termArg(0), k.floor());

      push(floorIntVars, a, k - k.floor());
      insertVar(out.mixVarSet, a.termArg(0), k - k.floor());
    }

    RStack<Monom> floorMixVars;
    for (auto [a, k] : arrayIter(*s.mixVars)) {
      push(out.mixVars, a, Numeral(k.floor()));
      push(floorMixVars, a, k - k.floor());
    }

    RStack<Monom> floorIntAtoms;
    for (auto [a, k] : arrayIter(*s.intAtoms)) {
      push(out.intAtoms, a, Numeral(k.floor()));
      push(floorIntAtoms, a, k - k.floor());
    }

    RStack<Monom> floorRatAtoms = std::move(s.ratAtoms);
    RStack<Monom> floorRatVars  = std::move(s.ratVars);

    auto floorVarSummands = [&]() {
      return concatIters(
                arrayIter(*floorIntVars),
                arrayIter(*floorMixVars),
                arrayIter(*floorRatVars)); };

    auto floorSummands = [&]() {
      return concatIters(
                arrayIter(*floorIntAtoms),
                arrayIter(*floorRatAtoms),
                floorVarSummands()); };

    auto makeFloor = [&]() {
      auto t = sum(au.subs(), floorSummands());
      return std::make_pair(TermSpec(ASig::floor(t.term), t.index), Numeral(1));
    };
    if ( floorSummands().size() == 1 
      && floorRatVars->size() == 1
      && floorRatVars[0].second == 1) {
      out.intVarSet->insert(floorRatVars[0].first.varSpec());
      out.intVars->push(makeFloor());
      ASS(ASig::isFloor(out.intVars[0].first.term) && out.intVars[0].first.term.term()->termArg(0).isVar());
    } else if (floorSummands().size() == 0) {
      /* nothing to add */
    } else if (floorVarSummands().size() == 0) {
      out.intAtoms->push(makeFloor());
    } else {
      for (auto &[v, k] : *floorRatVars) {
        out.mixVarSet->insert(v.varSpec());
      }
      out.mixVars->push(makeFloor());
    }

    return out;
  }

  static FloorUwaState scanAdd(AbstractingUnifier& au, TermSpec const& t0, TermSpec const& t1) { return add(au, scan(au, t0), scan(au, t1)); }
  static FloorUwaState scanFloor(AbstractingUnifier& au, TermSpec const& dt) { return floor(au, scan(au, dt)); }

  static FloorUwaState _mul(AbstractingUnifier& au, Numeral const& k, FloorUwaState s) {
    if (k == 0) {
      return FloorUwaState::zero();
    } else {
      auto procArray = [&](auto& sum) { 
        for (auto& s : sum) {
          s.second *= k;
        }
      };
      procArray(*s.ratVars);
      procArray(*s.intVars);
      procArray(*s.mixVars);
      procArray(*s.ratAtoms);
      procArray(*s.intAtoms);
      return s;
    }
  }

  static FloorUwaState mul(AbstractingUnifier& au, Numeral const& k, FloorUwaState s) {
    auto out = _mul(au, k, std::move(s));
    return out;
  }


  static FloorUwaState scanMul(AbstractingUnifier& au, Numeral const& k, TermSpec t) 
  { return k == 0 ? FloorUwaState::zero() : mul(au, k, scan(au, t)); }


  static FloorUwaState scan(AbstractingUnifier& au, TermSpec const& t) {
    auto &subs = au.subs();
    ASS_EQ(subs.derefBound(t), t)
    auto deref = [&](auto t2) { return subs.derefBound(TermSpec(t2, t.index)); };
    auto res = 
      optionIfThenElse(
            [&]() { return ASig::ifAdd(t.term, [&](auto l, auto r) { return scanAdd(au, deref(l), deref(r)); }); }
          , [&]() { return someIf(t.term == ASig::one(), [&]() { return one(au); }); }
          , [&]() { return ASig::ifLinMul(t.term, [&](auto& k, auto t) { return scanMul(au, k, deref(t)); }); }
          , [&]() -> Option<FloorUwaState> { 
              if (auto numeral = ASig::tryNumeral(t.term)) {
                return some(mul(au, *numeral, one(au)));
              } else {
                return {};
              }
            }
          , [&]() { return ASig::ifFloor(t.term, [&](auto t) { return scanFloor(au, deref(t)); }); }
          , [&]() {
              ASS(t.term.isVar() || ASig::isUninterpreted(t.term))
              auto out = FloorUwaState();
              if (t.term.isVar()) {
                out.ratVars->push(std::make_pair(t, Numeral(1)));
                out.ratVarSet->insert(t.varSpec());
              } else {
                out.ratAtoms->push(std::make_pair(t, Numeral(1)));
                BottomUpEvaluation<AutoDerefTermSpec, std::tuple<>>()
                    .function([&](auto const& orig, std::tuple<>* args) -> std::tuple<> {
                        if (orig.term.isVar()) {
                          out.shieldedVars->insert(orig.term.varSpec());
                        }

                        return {};
                    })
                    .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(), [&]() { return std::make_tuple(); }); })
                    .context(AutoDerefTermSpec::Context { .subs = &subs, })
                    .apply(AutoDerefTermSpec(t, &subs));
              }
              return out;
            });
    ASS(res.summands().all([](auto s) { return s.second != 0; }))
    return res;
  }

  bool hasTopVars() const { return !ratVars->isEmpty() || !intVars->isEmpty() || !mixVars->isEmpty(); }

  auto summands() const 
  { return concatIters(
          arrayIter(*ratVars), 
          arrayIter(*intVars), 
          arrayIter(*mixVars), 
          arrayIter(*ratAtoms), 
          arrayIter(*intAtoms)); }


  IterTraits<VirtualIterator<Monom>> summandsFloor() const 
    ;

  auto summandsInt() const 
  { return concatIters(
          arrayIter(*intVars), 
          arrayIter(*mixVars), 
          arrayIter(*intAtoms)); }

  auto summandsNotInt() const 
  { return concatIters(
          arrayIter(*ratVars), 
          arrayIter(*ratAtoms)); }

  Option<Numeral> gcd() const 
  {
    ASS(size() > 0)
    if (ratVars.size() != 0 || ratAtoms.size() != 0) {
      return {};
    } else {
      return some(summands()
        .map([](auto x) { return x.second; })
        .fold([](auto l, auto r) { return Numeral(l.numerator().gcd(r.numerator()), 
                                                  l.denominator().lcm(r.denominator())); })
        .unwrap());
    }
  }

  struct Bucket {
    Bucket() : _sum(0) {}
    Numeral _sum;
    RStack<Monom> _summands;
    auto summands() const { return arrayIter(*_summands); }
    auto& sum() const { return _sum; }
    void push(Monom m) { 
      _sum += m.second; 
      _summands->push(std::move(m)); 
    }
    auto positive() const { return summands().filter([](auto& x) { return x.second > 0; }); }
    auto negative() const { return summands().filter([](auto& x) { return x.second < 0; }); }
    static unsigned hash(Term* t) { 
      return ASig::ifLinMul(t, [](auto& k, auto t) { return hash(t.term()); })
          || ASig::ifFloor(t, [](auto t) { return 2 * hash(t.term()) + 1; })
          || ASig::ifAdd(t, [](auto l, auto r) { return hash(l.term()) + hash(r.term()); })
          || [&]() { return 2 * t->functor(); };
    }
    static unsigned hash(TermSpec t) { return hash(t.term.term()); }

    friend std::ostream& operator<<(std::ostream& out, Bucket const& self)
    { return out << Output::interleaved(" + ", self.summands()); }
  };

  auto buckets() const {
    Recycled<Map<unsigned, Bucket>> buckets;
    ASS(ratVars->isEmpty())
    ASS(intVars->isEmpty())
    ASS(mixVars->isEmpty())
    for (auto a : summands()) {
      auto &[t, k] = a;
      ASS(k != 0)
      buckets->getOrInit(Bucket::hash(t)).push(a);
    }

    auto allZero = iterTraits(buckets->iter()).all([](auto& b) { return b.value().sum() == 0; });

    return someIf(allZero,
        [&]() {
          return iterTraits(buckets->iter())
              .store(std::move(buckets))
              .map([](auto& x) { return std::move(x.value()); });
        });
  }
};



template<class Numeral>
TermSpec numMul(Numeral num, TermSpec t) 
{ return TermSpec(AlascaSignature<NumTraits<Numeral>>::linMul(num, t.term), t.index); }


template<class Iter>
TermSpec sum(RobSubstitution& subs, Iter iter) {
    using ASig = AlascaSignature<::NumTraits<typename std::remove_reference_t<std::remove_const_t<typename Iter::Elem>>::second_type>>;
    return iterTraits(std::move(iter))
      .map([&](auto x) { return numMul(x.second, std::move(x.first)); })
      .fold([&](auto l, auto r) 
        { return subs.createTerm(ASig::addF(), std::move(l), std::move(r)); })
      .unwrapOrElse([&]() { return TermSpec(ASig::numeralTl(ASig::constant(0)), 0); }); 
}

template<class F, class... Fs>
auto optionIfThenElse(F f, Fs... fs) 
{ return (f() || ... || fs); }

template<class NumTraits>
AbstractionOracle::AbstractionResult uwa_floor(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n_, Options::UnificationWithAbstraction uwa) {
  TIME_TRACE("unification with abstraction ALASCA+F")
  AlascaSignature<NumTraits> sig;
  Option<UnificationConstraint> sortsUnif;
  auto equalIf = [&]() {
    if (sortsUnif.isSome()) {
      return AbstractionOracle::EqualIf()
                     .unify(*sortsUnif.take());
    } else {
      return AbstractionOracle::EqualIf();
    }
  };
  using AbstractionResult = AbstractionOracle::AbstractionResult;
  using NeverEqual = AbstractionOracle::NeverEqual;
  using Numeral = typename NumTraits::ConstantType;

  auto constraint = [&](TermSpec lhs, TermSpec rhs) { return UnificationConstraint(lhs, rhs, TermSpec(sig.sort(), 0)); };
  auto constraint0 = [&](TermSpec x) { return constraint(x, TermSpec(sig.numeralTl(0), 0)); };
  auto sum = [&](auto iter) -> TermSpec { return ::sum(au.subs(), std::move(iter)); };

#define CHECK_SORTS(t1, t2)                                                               \
  if (t1.isTerm()) {                                                                      \
    auto s1 = au.subs().derefBound(t1.sort());                                            \
    if (s1.isVar()) {                                                                     \
      ASS(sortsUnif.isNone())                                                             \
      sortsUnif = some(UnificationConstraint(s1, TermSpec(sig.sort(), 0), TermSpec(AtomicSort::superSort(), 0))); \
    } else if (s1.term != sig.sort()) {                                                   \
      return AbstractionResult(NeverEqual{});                                             \
    }                                                                                     \
  }                                                                                       \

  CHECK_SORTS(t1, t2)
  CHECK_SORTS(t2, t1)

  using FUA = FloorUwaState<AlascaSignature<NumTraits>>;

  auto const diff = FUA::add(au, FUA::scan(au, t1), FUA::mul(au, Numeral(-1), FUA::scan(au, t2)));

  return optionIfThenElse(
      [&]() -> Option<AbstractionResult> { return someIf(diff.size() == 0, [equalIf]() { return AbstractionResult(equalIf()); }); },
      [&]() -> Option<AbstractionResult> {
            if (auto v = arrayIter(*diff.ratVars)
                           .find([&](auto& v) { return !diff.isShielded(v.first) && !diff.isMixVar(v.first); })) {
                //     k x   + t1 + ... + tn  = 0
                // <-> k x = - t1 - ... - tn
                // <->   x = (- t1/k - ... - tn/k)
                auto& k = v->second;
                auto& x = v->first;
                return some(AbstractionResult(equalIf().unify(constraint(
                        x, 
                        sum(diff.summands() 
                                 .filter([&](auto s) { /* filter out k x */ return s != *v; })
                                 .map([&](auto s) { return std::make_pair(s.first, -s.second / k); })
                        )))));
            } else {
              return {};
            }
          },
      [&]() { return someIf(diff.hasTopVars(), [&]() { 
        return optionIfThenElse(
            [&]() -> Option<AbstractionResult> { 
              if (diff.size() == 2 && diff.summandsInt().size() == 2) {

                auto oneCase = [&](auto s0, auto s1) -> Option<AbstractionResult> {
                  auto [one, k] = s0;
                  auto [t, kt] = s1;
                  if (one.term == sig.one()) {
                    ASS(sig.isFloor(t.term))
                    if ((k / kt).isInt()) {
                      return some(AbstractionResult(equalIf().unify(constraint(t.termArg(0), TermSpec(sig.numeralTl(-(k / kt)), 0)))));
                    } else {
                      return some(AbstractionResult(NeverEqual{}));
                    }
                  } else {
                    return {};
                  }
                };

                // this case does not work as we'd need to potentially return two unifiers
                // floor(x) = floor(a) <-> x = a | x = floor(a)
                // auto case1 = [&](auto s0, auto s1) -> Option<AbstractionResult> {
                //   auto [t0, k0] = s0;
                //   auto [t1, k1] = s1;
                //   ASS(sig.isFloor(t0.term))
                //   ASS(sig.isFloor(t1.term))
                //   if (k0 != -k1) {
                //     return {};
                //   } else {
                //     return some(AbstractionResult(equalIf().unify(constraint(t0.termArg(0), t1.termArg(0)))));
                //   }
                //   // auto [one, k] = s0;
                //   // auto [t, kt] = s1;
                //   // if (sig.tryNumeral(one.term) == some(Numeral(1))) {
                //   //   ASS(sig.isFloor(t.term))
                //   //   if ((k / kt).isInt()) {
                //   //     return some(AbstractionResult(equalIf().unify(constraint(t.termArg(0), TermSpec(sig.numeralTl(-(k / kt)), 0)))));
                //   //   } else {
                //   //     return some(AbstractionResult(NeverEqual{}));
                //   //   }
                //   // } else {
                //   //   return {};
                //   // }
                // };

                auto iter = diff.summandsInt();
                auto s0 = iter.next();
                auto s1 = iter.next();

                return optionIfThenElse( [&]() { return oneCase(s0, s1); }
                                       , [&]() { return oneCase(s1, s0); }
                    );
              } else {
                return {};
              }
            },
            [&]() { return AbstractionResult(equalIf().constr(constraint0(sum(diff.summands())))); }); 
      }); },
      [&]() { return someIf(diff.hasTopVars(), [&]() { return AbstractionResult(equalIf().constr(constraint0(sum(diff.summands())))); }); },
      [&]() { 
          /* no top vars */
          if (auto buckets = diff.buckets()) {
            auto eqIf = equalIf();
            for (auto b : *buckets) {
              if (b.summands().size() == 2) {
                auto [t0_, k0, t1, k1] = tuple_flatten(b.summands().template collectTuple<2>());
                auto t0 = t0_;
                ASS_EQ(t0.functor(), t1.functor())
                ASS_EQ(k0, -k1)
                /* unwrap */
                eqIf.unify().loadFromIterator(
                    t0.allArgs().zip(t1.allArgs()).zip(range(0, t0.nAllArgs()))
                      .map([&](auto pair) { return UnificationConstraint(pair.first.first, pair.first.second, t0.anyArgSort(pair.second)); }));
              } else {
                eqIf.constr().push(constraint(
                  sum(b.positive()),
                  sum(b.negative().map([](auto t) { return std::make_pair(t.first, -t.second); }))
                ));
              }
            }
            return AbstractionResult(std::move(eqIf));
          } else {
            return AbstractionResult(NeverEqual{});
          }
      });
}


Option<AbstractionOracle::AbstractionResult> AbstractionOracle::tryAbstract(AbstractingUnifier* au, TermSpec const& t1, TermSpec const& t2) const
{
  ASS(_mode != Shell::Options::UnificationWithAbstraction::OFF)

  if (_mode == Shell::Options::UnificationWithAbstraction::FUNC_EXT) {
    return funcExt(au, t1, t2);

  } else if (_mode == Shell::Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR) {
    return uwa_floor(*au, t1, t2, _mode);

  } else if (_mode == Shell::Options::UnificationWithAbstraction::ALASCA_MAIN
      || _mode == Shell::Options::UnificationWithAbstraction::ALASCA_CAN_ABSTRACT
      || _mode == Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP
      ) {
    return alasca(*au, t1, t2, _mode);

  } else {
    auto abs = canAbstract(au, t1, t2);
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
    DEBUG_FINALIZE(2, "todo: ", todo);
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

Option<Recycled<Stack<unsigned>>> AbstractingUnifier::unifiableSymbols(SymbolId fid)
{
  auto f = fid.functor;
  if (fid.kind == TermKind::SORT)
    // we don't perform UWA on sorts
    return some(recycledStack(f));

  ASS(fid.kind == TermKind::TERM) // not implemented for literals

  auto anything = []() -> Option<Recycled<Stack<unsigned>>> { return {}; };
  auto nothing  = []() -> Option<Recycled<Stack<unsigned>>> { return some(recycledStack<unsigned>()); };
  switch (_uwa._mode) {
    case Options::UnificationWithAbstraction::AUTO:
      ASSERTION_VIOLATION_REP("UnificationWithAbstraction::AUTO should have been resolved to a concrete value by now")
    case Options::UnificationWithAbstraction::OFF: return some(recycledStack(f));
    case Options::UnificationWithAbstraction::INTERP_ONLY: return theory->isInterpretedFunction(f) ? anything() : some(recycledStack(f));
    case Options::UnificationWithAbstraction::ONE_INTERP: return anything();
    case Options::UnificationWithAbstraction::CONSTANT: return theory->isInterpretedConstant(f) ? anything() : nothing();
    case Options::UnificationWithAbstraction::ALL: return anything();
    case Options::UnificationWithAbstraction::GROUND: anything();
    case Options::UnificationWithAbstraction::FUNC_EXT: anything();
    case Options::UnificationWithAbstraction::ALASCA_CAN_ABSTRACT:
    case Options::UnificationWithAbstraction::ALASCA_ONE_INTERP:
    case Options::UnificationWithAbstraction::ALASCA_MAIN: return isAlascaInterpreted(f) ? anything() : some(recycledStack(f));
    case Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR: return isAlascaiInterpreted(f) ? anything() : some(recycledStack(f));
  }
  ASSERTION_VIOLATION
}

bool AbstractingUnifier::unify(TermList term1, int bank1, TermList term2, int bank2)
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
      DEBUG_UNIFY(2, "todo:   ", toDo);
      auto cur = toDo->pop();
      DEBUG_UNIFY(2, "popped: ", cur)
      auto dt1 = subs().derefBound(cur.first);
      auto dt2 = subs().derefBound(cur.second);
      DEBUG_UNIFY(1, "deref:  ", dt1, " ?= ", dt2)
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
            DEBUG_UNIFY(3, "uwa adding unify : ", pair)
          }
          for (auto& x: conditions.constr()) {
            _constr->add(std::move(x), bd());
            DEBUG_UNIFY(3, "uwa adding constr: ", x)
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




