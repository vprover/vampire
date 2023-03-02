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
 * @file MismatchHandler.cpp
 * Defines class MismatchHandler.
 *
 */

#include "Lib/Backtrackable.hpp"
#include "Lib/Coproduct.hpp"
#include "Lib/Metaiterators.hpp"
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/SortHelper.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/QKbo.hpp"
#include <functional>


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "Kernel/NumTraits.hpp"

#include "MismatchHandler.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Debug/Output.hpp"
#define DEBUG_UWA(LVL, ...)   if (LVL <= 0) DBG(__VA_ARGS__)
#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
// increase this number to increase  <---^
// debug verbosity
#define DEBUG_FINALIZE(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)

namespace Kernel
{

  
// pair<TermList, int>& TermSpec::deref()
// { return _deref.unwrapOrInit([&]() { 
//     auto t = _subs->derefBound(RobSubstitution::TermSpec(_term, _index));
//     return make_pair(t.term, t.index);
//   }); }

// TermSpec TermSpec::termArg(unsigned i)
// { return TermSpec(*_subs, term()->termArg(i), index(i + nTypeArgs())); }

// TermSpec::TermSpec(RobSubstitution& subs, TermList term, int index) //   : _subs(&subs)
//   , _self(make_pair(term, index))
// {
// }


// TermSpec TermSpec::typeArg(unsigned i)
// { return TermSpec(*_subs, term()->typeArg(i), index(i)); }

Shell::Options::UnificationWithAbstraction MismatchHandler::create()
{
  if (env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF) {
    return env.options->unificationWithAbstraction();
  } else if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.property->higherOrder()) { 
    // TODO  ask ahmed: are this the corret options for higher order abstraction
    return Options::UnificationWithAbstraction::FUNC_EXT;
  } else {
    return Options::UnificationWithAbstraction::OFF;
  }
}

Shell::Options::UnificationWithAbstraction MismatchHandler::createOnlyHigherOrder()
{
  if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.property->higherOrder()) { 
    // TODO  ask ahmed: are this the corret options for higher order abstraction
    return Options::UnificationWithAbstraction::FUNC_EXT;
  } else {
    return Options::UnificationWithAbstraction::OFF;
  }
}

bool MismatchHandler::isInterpreted(unsigned functor) const 
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
    auto* dt = &t.deref(_subs);
    while (dt->isTerm() && dt->functor() == _function) {
      ASS_EQ(dt->nTermArgs(), 2);
      _todo->push(dt->termArg(1));
      t = dt->termArg(0);
      dt = &t.deref(_subs);
    }
    return dt->clone();
  }
};
template<class NumTraits>
MismatchHandler::AbstractionResult alasca4(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n) {
  TIME_TRACE("unification with abstraction ALASCA3")
  using EqualIf = MismatchHandler::EqualIf;
  using AbstractionResult = MismatchHandler::AbstractionResult;
  using NeverEqual = MismatchHandler::NeverEqual;
  using Numeral = typename NumTraits::ConstantType;

  TermSpec one = TermSpec(TermList(n.one()), 0);

  auto atoms = [&](auto& term) {
    return iterTraits(AcIter(NumTraits::addF(), term.clone(), &au.subs()))
      .map([&](TermSpec out) -> pair<TermSpec, Numeral> {
          // auto out = make_pair(std::move(t), one.clone());
          auto numeral = Numeral(1);
          while (true) {
            if (out.isVar()) 
              return make_pair(out.clone(), std::move(numeral));

            auto f = out.functor();
            if (n.isMinus(f)) {
              out = out.termArg(0).deref(&au.subs()).clone();
              numeral = -numeral;
            }
            auto num = n.tryNumeral(f);
            if (num.isSome()) {
              return make_pair(one.clone(), numeral * (*num));

            } else if (n.isMul(f)) {
              auto lhs_ = out.termArg(0);
              auto rhs_ = out.termArg(1);
              auto& lhs = lhs_.deref(&au.subs());
              auto& rhs = rhs_.deref(&au.subs());;
              if (lhs.isTerm() && n.isNumeral(lhs.functor())) {
                out = rhs.clone();
                numeral = numeral * (*n.tryNumeral(lhs.functor()));
              } else if (rhs.isTerm() && n.isNumeral(rhs.functor())) {
                out = lhs.clone();
                numeral = numeral * (*n.tryNumeral(rhs.functor()));
              } else {
                // non-linear multiplication
                return make_pair(std::move(out), numeral);
              }
            } else {
              // uninterpreted
              return make_pair(std::move(out), numeral);
            }
          }
       });
  };

  Recycled<Stack<pair<TermSpec, Numeral>>> _diff;
  auto& diff = *_diff;
  DEBUG_UWA(2, "diff: ", diff, " (0)");
  diff.loadFromIterator(concatIters(
    atoms(t1),
    atoms(t2).map([](auto x) { return make_pair(std::move(x.first), -x.second); })
  ));
  DEBUG_UWA(2, "diff: ", diff, " (1)");

  auto sumUp = [](auto& diff, auto cmp) {
    auto i1 = 0;
    auto i2 = 1;
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

  auto cmp = [&au](auto const& t1, auto const& t2) { 
    TIME_TRACE("comparing TermSpecs")
    auto top1 = t1.top();
    auto top2 = t2.top();
    auto v1 = !t1.isVar();
    auto v2 = !t2.isVar();
    if (std::tie(v1, top1) == std::tie(v2, top2)) {
      return TermSpec::compare(t1, t2, [&au](auto& t) -> decltype(auto) { return t.deref(&au.subs()); });
    } else {
      return std::tie(v1, top1) < std::tie(v2, top2) ? -1 : 1;
    }
  };
  // auto less = [](auto const& t1, auto const& t2) { 
  //   TIME_TRACE("comparing TermSpecs")
  //   auto top1 = t1.top();
  //   auto top2 = t2.top();
  //   auto v1 = !t1.isVar();
  //   auto v2 = !t2.isVar();
  //   return std::tie(v1, top1, t1) < std::tie(v2, top2, t2);
  // };
  diff.sort([&](auto& l, auto& r) { return cmp(l.first, r.first) < 0; });
  DEBUG_UWA(2, "diff: ", diff, " (before summing up )");
  sumUp(diff, cmp);
  DEBUG_UWA(2, "diff: ", diff, " (after summing up )");

  // auto vars = arrayIter(diff)
  //               .takeWhile([](auto& x) { return x.first.isVar(); });

  // TODO bin search if many elems
  auto nVars = range(0, diff.size())
    .find([&](auto i) { return !diff[i].first.isVar();  })
    .unwrapOrElse([&](){ return diff.size(); });


  ASS(nVars == 0 || diff[nVars - 1].first.isVar())
  ASS(nVars == diff.size() || !diff[nVars].first.isVar())


  auto numMul = [](Numeral num, TermSpec t) {
    ASS(num != Numeral(0))
    if (num == Numeral(1)) {
      return std::move(t);

    } else if (num == Numeral(-1)) {
      return TermSpec(NumTraits::minusF(), std::move(t));

    } else {
      return TermSpec(NumTraits::mulF(), 
          TermSpec(NumTraits::numeralF(num)),
          std::move(t)
      );
    }
  };

  auto sum = [&](auto iter) -> TermSpec {
      return iterTraits(std::move(iter))
        .map([&](auto x) { return numMul(x.second, std::move(x.first)); })
        .fold([](auto l, auto r) 
          { return TermSpec(NumTraits::addF(), std::move(l), std::move(r)); })
        .unwrapOrElse([&]() { return TermSpec(NumTraits::numeralF(Numeral(0))); }); };

  // auto diffConstr = [&]() 
  // { return UnificationConstraint(sum(diff1), sum(diff2)); };

  auto toConstr = [&](auto& stack) {
    return UnificationConstraint(
              sum(arrayIter(stack)
                 .filter([](auto& x) { return x.second.isPositive(); })
                 .map([](auto& x) { return make_pair(std::move(std::move(x.first)), x.second); })),
              sum(arrayIter(stack)
                 .filter([](auto& x) { return !x.second.isPositive(); })
                 .map([](auto& x) { return make_pair(std::move(x.first), -x.second); }))
              );
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
       todo->push(diff[i].first.clone());
       while (todo->isNonEmpty()) {
         auto next_ = todo->pop();
         auto& next = next_.deref(&au.subs());
         if (next.isVar()) {
           shieldedVars->insert(next.clone());
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
            [&](auto n) { return EqualIf().unify(UnificationConstraint(numMul(-num, std::move(var)), sum(rest()))); },
            [&](auto n) { return EqualIf().unify(UnificationConstraint(std::move(var), 
                sum(rest().map([&](auto x) { return make_pair(std::move(x.first), divOrPanic(n, x.second, -num)); })
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

  Recycled<Stack<UnificationConstraint>> unify;
  Recycled<Stack<UnificationConstraint>> constr;
  auto curF = diff[0].first.functor();
  Recycled<Stack<pair<TermSpec, Numeral>>> curSummands;
  auto curSum = Numeral(0);  


  auto curSumCanUnify = [&]() -> bool {
      if (curSum != Numeral(0)) {
        return false;
      } else if (curSummands->size() == 2) {
        auto& pos = (*curSummands)[0].second.isPositive() ? (*curSummands)[0] : (*curSummands)[1];
        auto& neg = (*curSummands)[0].second.isPositive() ? (*curSummands)[1] : (*curSummands)[0];
        ASS(pos.second.isPositive())
        ASS(neg.second.isNegative())
        unify->push(UnificationConstraint(
              numMul( pos.second, std::move(pos.first)), 
              numMul(-neg.second, std::move(neg.first))));
        return true;
      } else {
        ASS(curSummands->size() >= 3)
        constr->push(toConstr(*curSummands));
        return true;
      }
  };

  for (auto& x : diff) {
    auto f = x.first.functor();
    if (f != curF) {
      if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
      curF = f;
      curSum = Numeral(0);
      curSummands->reset();
    }
    curSum += x.second;
    curSummands->push(std::move(x));
  }
  if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
  return AbstractionResult(EqualIf().unify(std::move(unify)).constr(std::move(constr)));
}

bool uncanellableOccursCheck(AbstractingUnifier& au, VarSpec const& v, TermSpec const& t) {

  if (t.isSort()) return true; // <- for sorts arguments might never cancel out
  Recycled<Stack<TermSpec>> todo;
  ASS(t.isTerm())
  todo->push(t.clone());
  while (!todo->isEmpty()) {
    auto t = todo->pop();
    auto& dt = t.deref(&au.subs());
    if (dt.isTerm()) {
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

Option<MismatchHandler::AbstractionResult> alasca4(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2) {
  ASS(t1.isTerm() || t2.isTerm())

  auto interpreted = [](TermSpec const& t) {
    if (t.isVar()) return false;
    ASS(!t.isLiteral()) 
    auto f = t.functor();
    return forAnyNumTraits([&](auto numTraits) -> bool {
        return numTraits.isAdd(f)
            || numTraits.isNumeral(f)
            || numTraits.isMinus(f)
            || numTraits.isMul(f);
    });
  };


  // if (t1.isVar()) return occ(t1, t2);
  // if (t2.isVar()) return occ(t2, t1);

  if ((t1.isTerm() && t1.isSort()) 
  || ( t2.isTerm() && t2.isSort())) return {};

  auto i1 = interpreted(t1);
  auto i2 = interpreted(t2);
  if (i1 || i2) {
    TermList sort = (i1 ? t1.sort() : t2.sort()).old().term;
    return forAnyNumTraits([&](auto n) {
        return someIf(sort == n.sort(), [&]() { return alasca4(au, t1, t2, n); });
    });
  } else {
    auto occ = [&au](auto& v, auto& t) {
      ASS(v.isVar())
      ASS(t.isTerm())
      // we know due to the uwa algorithm that v occurs in t
      if (uncanellableOccursCheck(au, v.varSpec(), t)) {
        return some(MismatchHandler::AbstractionResult(MismatchHandler::NeverEqual{}));
      } else {
        // this means all
        return some(MismatchHandler::AbstractionResult(MismatchHandler::EqualIf().constr(UnificationConstraint(v.clone(), t.clone()))));
      }
    };

    if (t1.isVar()) return occ(t1, t2);
    if (t2.isVar()) return occ(t2, t1);
    return {};
  }
}
bool isAlascaInterpreted(TermSpec const& t, AbstractingUnifier& au) {
  if (t.isVar()) return false;
  ASS(!t.isLiteral()) 
  auto f = t.functor();
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return numTraits.isAdd(f)
          || numTraits.isNumeral(f)
          || numTraits.isMinus(f)
          || (numTraits.isMul(f)
              && (t.termArg(0).deref(&au.subs()).isTerm() 
              && numTraits.isNumeral(t.termArg(0).deref(&au.subs()).functor())));
  });
};

bool MismatchHandler::canAbstract(AbstractingUnifier* au, TermSpec const& t1, TermSpec const& t2) const 
{
  if( ( t1.isTerm() && t1.isSort() ) 
   || ( t2.isTerm() && t2.isSort() ) ) return false;

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
    case Shell::Options::UnificationWithAbstraction::ALASCA1: 
      return isAlascaInterpreted(t1, *au) || isAlascaInterpreted(t2, *au);
    case Shell::Options::UnificationWithAbstraction::ALASCA2: {

        TIME_TRACE("unification with abstraction ALASCA2")
        // TODO get rid of globalState
        auto shared = LascaState::globalState;

        if (t1.isVar() && t2.isVar()) return true;
        TermSpec sort;
        if (t1.isTerm() && t2.isTerm()) {
          sort = t1.sort();
          if (t2.sort().old().term != sort.old().term) {
            return false;
          }

        } else {
          sort = t1.isTerm() ? t1.sort() : t2.sort();
        }
        ASS(!t1.isLiteral())
        ASS(!t2.isLiteral())

        if (!isAlascaInterpreted(t1, *au) && !isAlascaInterpreted(t2, *au))
          return false;

        auto canAbstract = forAnyNumTraits([&](auto numTraits) {
            if (numTraits.sort() == sort.old().term) {
                // TODO get rid of toTerm here
                auto a1 = shared->signedAtoms<decltype(numTraits)>(t1.toTerm(au->subs()));
                auto a2 = shared->signedAtoms<decltype(numTraits)>(t2.toTerm(au->subs()));

                if (a1.isNone() || a2.isNone()) 
                  return Option<bool>(true);

                // we have s or t being a sum `k x + ... `
                if (concatIters(a1.unwrap().elems.iter(), a2.unwrap().elems.iter())
                       .any([&](auto& x) { return get<0>(x).term.isVar(); }))
                  return Option<bool>(true);

                return Option<bool>(Ordering::Result::EQUAL == OrderingUtils2::weightedMulExt(
                    a1.unwrap(),
                    a2.unwrap(),
                    [](auto& l, auto& r) { return (l.sign == r.sign && l.term.term()->functor() == r.term.term()->functor())
                      ? Ordering::Result::EQUAL
                      : Ordering::Result::INCOMPARABLE; }));
            } else {
                return Option<bool>();
            }
        });

        return canAbstract.unwrap();

    }
    case Shell::Options::UnificationWithAbstraction::OFF:
      return false;
    case Shell::Options::UnificationWithAbstraction::AC1: 
    case Shell::Options::UnificationWithAbstraction::AC2: 
    case Shell::Options::UnificationWithAbstraction::ALASCA3: 
    case Shell::Options::UnificationWithAbstraction::ALASCA4: 
    case Shell::Options::UnificationWithAbstraction::FUNC_EXT: 
      ASSERTION_VIOLATION_REP("should be handled in MismatchHandler::tryAbstract")
  }
  ASSERTION_VIOLATION;
}

template<class NumTraits>
typename NumTraits::ConstantType divOrPanic(NumTraits n, typename NumTraits::ConstantType c1, typename NumTraits::ConstantType c2) { return c1 / c2; }
typename IntTraits::ConstantType divOrPanic(IntTraits n, typename IntTraits::ConstantType c1, typename IntTraits::ConstantType c2) { ASSERTION_VIOLATION }

template<class NumTraits>
MismatchHandler::AbstractionResult alasca3(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2, NumTraits n) {
  TIME_TRACE("unification with abstraction ALASCA3")
  using EqualIf = MismatchHandler::EqualIf;
  using AbstractionResult = MismatchHandler::AbstractionResult;
  using NeverEqual = MismatchHandler::NeverEqual;
  using Numeral = typename NumTraits::ConstantType;

  TermSpec one = TermSpec(TermList(n.one()), 0);

  auto atoms = [&](auto& t) {
    return iterTraits(AcIter(NumTraits::addF(), t.clone(), &au.subs()))
      .map([&](TermSpec t) -> pair<TermSpec, Numeral> {
          if (t.isVar()) 
            return make_pair(t.clone(), Numeral(1));
          auto f = t.functor();
          if (n.isMinus(f)) 
            return make_pair(t.termArg(0).deref(&au.subs()).clone(), Numeral(-1));
          auto num = n.tryNumeral(f);
          if (num.isSome()) {
            return make_pair(one.clone(), *num);
          } else {
            if (n.isMul(f)) {
                auto lhs = t.termArg(0).deref(&au.subs()).clone();
                auto lnum = someIf(lhs.isTerm(), 
                    [&]() { return n.tryNumeral(lhs.functor()); })
                    .flatten();
                if (lnum) {
                   return make_pair(t.termArg(1).deref(&au.subs()).clone(), *lnum);
                }
            }
            return make_pair(t.clone(), Numeral(1));
          }
          });
  };

  Recycled<Stack<pair<TermSpec, Numeral>>> _diff;
  auto& diff = *_diff;
  DEBUG_UWA(2, "diff: ", diff, " (0)");
  diff.loadFromIterator(concatIters(
    atoms(t1),
    atoms(t2).map([](auto x) { return make_pair(std::move(x.first), -x.second); })
  ));
  DEBUG_UWA(2, "diff: ", diff, " (1)");

  auto sumUp = [](auto& diff, auto cmp) {
    auto i1 = 0;
    auto i2 = 1;
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

  auto cmp = [&au](auto const& t1, auto const& t2) { 
    TIME_TRACE("comparing TermSpecs")
    auto top1 = t1.top();
    auto top2 = t2.top();
    auto v1 = !t1.isVar();
    auto v2 = !t2.isVar();
    if (std::tie(v1, top1) == std::tie(v2, top2)) {
      return TermSpec::compare(t1, t2, [&au](auto& t) -> decltype(auto) { return t.deref(&au.subs()); });
    } else {
      return std::tie(v1, top1) < std::tie(v2, top2) ? -1 : 1;
    }
  };
  // auto less = [](auto const& t1, auto const& t2) { 
  //   TIME_TRACE("comparing TermSpecs")
  //   auto top1 = t1.top();
  //   auto top2 = t2.top();
  //   auto v1 = !t1.isVar();
  //   auto v2 = !t2.isVar();
  //   return std::tie(v1, top1, t1) < std::tie(v2, top2, t2);
  // };
  diff.sort([&](auto& l, auto& r) { return cmp(l.first, r.first) < 0; });
  DEBUG_UWA(2, "diff: ", diff, " (before summing up )");
  sumUp(diff, cmp);
  DEBUG_UWA(2, "diff: ", diff, " (after summing up )");

  auto vars = arrayIter(diff)
                .takeWhile([](auto& x) { return x.first.isVar(); });

  auto numMul = [](Numeral num, TermSpec t) {
    ASS(num != Numeral(0))
    if (num == Numeral(1)) {
      return std::move(t);

    } else if (num == Numeral(-1)) {
      return TermSpec(NumTraits::minusF(), std::move(t));

    } else {
      return TermSpec(NumTraits::mulF(), 
          TermSpec(NumTraits::numeralF(num)),
          std::move(t)
      );
    }
  };

  auto sum = [&](auto iter) -> TermSpec {
      return iterTraits(std::move(iter))
        .map([&](auto x) { return numMul(x.second, std::move(x.first)); })
        .fold([](auto l, auto r) 
          { return TermSpec(NumTraits::addF(), std::move(l), std::move(r)); })
        .unwrapOrElse([&]() { return TermSpec(NumTraits::numeralF(Numeral(0))); }); };

  // auto diffConstr = [&]() 
  // { return UnificationConstraint(sum(diff1), sum(diff2)); };

  auto toConstr = [&](auto& stack) {
    return UnificationConstraint(
              sum(arrayIter(stack)
                 .filter([](auto& x) { return x.second.isPositive(); })
                 .map([](auto& x) { return make_pair(std::move(std::move(x.first)), x.second); })),
              sum(arrayIter(stack)
                 .filter([](auto& x) { return !x.second.isPositive(); })
                 .map([](auto& x) { return make_pair(std::move(x.first), -x.second); }))
              );
  };
  if (arrayIter(diff).any([&](auto& x) 
        { return x.first.isTerm() && n.isMul(x.first.functor()); })) {

    // non-linear multiplication. we cannot deal with this in alasca
    return AbstractionResult(EqualIf().constr(toConstr(diff)));

  } else if (diff.size() == 0) {
    return AbstractionResult(EqualIf());

  } else if ( vars.hasNext() ) {
    auto& v = vars.next();
    if (!vars.hasNext() || diff.size() == 2) {
      // ^^^^^^^^^^^^^^\   ^^^^^^^^^^^^^^^^-> two variables and nothing else
      //                +--> only one variable
      auto num = v.second;
      auto rest = [&]() 
      { return arrayIter(diff).filter([&](auto& x) { return x != v; }).map([](auto& x) { return std::move(x); }); };
      // { return arrayIter(diff).filter([&](auto& x) { return x != v; }).map([](auto& x) { return make_pair(x.first.clone(), x.second); }); };

      return AbstractionResult(ifIntTraits(n, 
          [&](auto n) { return EqualIf().unify(UnificationConstraint(numMul(-v.second, std::move(v.first)), sum(rest()))); },
          [&](auto n) { return EqualIf().unify(UnificationConstraint(std::move(v.first), 
                            sum(rest().map([&](auto x) { return make_pair(std::move(x.first), divOrPanic(n, x.second, -num)); })
                              ))); }
          ));
      ;
    } else {
      // multiplet variables
     return AbstractionResult(EqualIf().constr(toConstr(diff)));
    }
  } 

  Recycled<Stack<UnificationConstraint>> unify;
  Recycled<Stack<UnificationConstraint>> constr;
  auto curF = diff[0].first.functor();
  Recycled<Stack<pair<TermSpec, Numeral>>> curSummands;
  auto curSum = Numeral(0);  


  auto curSumCanUnify = [&]() -> bool {
      if (curSum != Numeral(0)) {
        return false;
      } else if (curSummands->size() == 2) {
        auto& pos = (*curSummands)[0].second.isPositive() ? (*curSummands)[0] : (*curSummands)[1];
        auto& neg = (*curSummands)[0].second.isPositive() ? (*curSummands)[1] : (*curSummands)[0];
        ASS(pos.second.isPositive())
        ASS(neg.second.isNegative())
        unify->push(UnificationConstraint(
              numMul( pos.second, std::move(pos.first)), 
              numMul(-neg.second, std::move(neg.first))));
        return true;
      } else {
        ASS(curSummands->size() >= 3)
        constr->push(toConstr(*curSummands));
        return true;
      }
  };

  for (auto& x : diff) {
    auto f = x.first.functor();
    if (f != curF) {
      if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
      curF = f;
      curSum = Numeral(0);
      curSummands->reset();
    }
    curSum += x.second;
    curSummands->push(std::move(x));
  }
  if (!curSumCanUnify()) return AbstractionResult(NeverEqual{});
  auto out = AbstractionResult(EqualIf().unify(std::move(unify)).constr(std::move(constr))); 
  return out;
}



Option<MismatchHandler::AbstractionResult> alasca3(AbstractingUnifier& au, TermSpec const& t1, TermSpec const& t2) {
  auto occ = [&au](auto& v, auto& t) {
    ASS(v.isVar())
    ASS(t.isTerm())
    // we know due to the uwa algorithm that v occurs in t
    if (uncanellableOccursCheck(au, v.varSpec(), t)) {
      return some(MismatchHandler::AbstractionResult(MismatchHandler::NeverEqual{}));
    } else {
      // this means all
      return some(MismatchHandler::AbstractionResult(MismatchHandler::EqualIf().constr(UnificationConstraint(v.clone(), t.clone()))));
    }
  };
  if (t1.isVar()) return occ(t1, t2);
  if (t2.isVar()) return occ(t2, t1);
  if (t1.isSort() || t2.isSort()) return {};
  auto i1 = isAlascaInterpreted(t1, au);
  auto i2 = isAlascaInterpreted(t2, au);
  return someIf(i1 || i2, [&]() {
    TermList sort = (i1 ? t1.sort() : t2.sort()).old().term;
    return forAnyNumTraits([&](auto n) {
        return someIf(sort == n.sort(), [&]() { return alasca3(au, t1, t2, n); });
    });
  }).flatten();
}

Option<MismatchHandler::AbstractionResult> funcExt(
    AbstractingUnifier* au, 
    TermSpec const& t1, TermSpec const& t2)
{
  CALL("HOMismatchHandler::tryAbstract")
  ASS(t1.isTerm() || t2.isTerm())
  ASS(!t1.isSpecialVar())
  ASS(!t2.isSpecialVar())

  auto isApp = [](auto& t) { return env.signature->isAppFun(t.functor()); };
  if ( (t1.isTerm() && t1.isSort()) 
    || (t2.isTerm() && t2.isSort()) ) return Option<MismatchHandler::AbstractionResult>();
  if (t1.isTerm() && t2.isTerm()) {
    if (isApp(t1) && isApp(t2)) {
      auto argSort1 = t1.typeArg(0).deref(&au->subs()).clone();
      auto argSort2 = t2.typeArg(0).deref(&au->subs()).clone();
      if (t1.isVar() || t2.isVar()
       || env.signature->isArrowCon(argSort1.functor())
       || env.signature->isArrowCon(argSort2.functor())
       ) {
        return some(MismatchHandler::AbstractionResult(MismatchHandler::EqualIf()
              .unify (UnificationConstraint(t1.termArg(0), t2.termArg(0)))
              .constr(UnificationConstraint(t1.termArg(1), t2.termArg(1)))));
      }
    }
  }
  return Option<MismatchHandler::AbstractionResult>();
}


Option<MismatchHandler::AbstractionResult> MismatchHandler::tryAbstract(AbstractingUnifier* au, TermSpec const& t1, TermSpec const& t2) const
{
  CALL("MismatchHandler::tryAbstract");
  TIME_TRACE("uwa tryAbstract");
  using Uwa = Shell::Options::UnificationWithAbstraction;
  ASS(_mode != Uwa::OFF)


  // TODO add parameter instead of reading from options
  if (_mode == Uwa::AC1 || _mode == Uwa::AC2) {
      if (!(t1.isTerm() && theory->isInterpretedFunction(t1.functor(), RatTraits::addI))
       || !(t2.isTerm() && theory->isInterpretedFunction(t2.functor(), RatTraits::addI))) {
        return Option<AbstractionResult>();
      }
      auto a1 = iterTraits(AcIter(RatTraits::addF(), t1.clone(), &au->subs())).template collect<Stack>();
      auto a2 = iterTraits(AcIter(RatTraits::addF(), t2.clone(), &au->subs())).template collect<Stack>();
      auto cmp = [&](TermSpec const& lhs, TermSpec const& rhs) { return TermSpec::compare(lhs, rhs, [&](auto& t) -> TermSpec const& { return t.deref(&au->subs()); }); };
      auto less = [&](TermSpec const& lhs, TermSpec const& rhs) { return cmp(lhs, rhs) < 0; };
      a1.sort(less);
      a2.sort(less);

      Recycled<Stack<TermSpec>> diff1_;
      Recycled<Stack<TermSpec>> diff2_;
      auto& diff1 = *diff1_;
      auto& diff2 = *diff2_;
      diff1.moveFromIterator(iterSortedDiff(arrayIter(a1), arrayIter(a2), cmp).map([](auto& x) -> TermSpec { return x.clone(); }));
      diff2.moveFromIterator(iterSortedDiff(arrayIter(a2), arrayIter(a1), cmp).map([](auto& x) -> TermSpec { return x.clone(); }));
      auto sum = [](auto& diff) {
          return arrayIter(diff)
            .map([](auto& x) { return x.clone(); })
            .fold([](auto l, auto r) 
              { return TermSpec(RatTraits::addF(), std::move(l), std::move(r)); })
            .unwrap(); };
      auto diffConstr = [&]() 
      { return UnificationConstraint(sum(diff1), sum(diff2)); };

      auto functors = [](auto& diff) 
      { return arrayIter(diff).map([](auto& f) { return f.functor(); }); };

      if (diff1.size() == 0 && diff2.size() == 0) {
        return some(AbstractionResult(EqualIf()));

      } else if (( diff1.size() == 0 && diff2.size() != 0 )
              || ( diff2.size() == 0 && diff1.size() != 0 ) ) {
        return some(AbstractionResult(NeverEqual{}));

      } else if (_mode == Uwa::AC2 && diff1.size() == 1 && diff1[0].isVar()) {
        return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff1[0]), sum(diff2)))));

      } else if (_mode == Uwa::AC2 && diff2.size() == 1 && diff2[0].isVar()) {
        return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff2[0]), sum(diff1)))));

      } else if (concatIters(arrayIter(diff1), arrayIter(diff2)).any([](auto& x) { return x.isVar(); })) {
        return some(AbstractionResult(EqualIf().constr(diffConstr())));

      } else if (iterSortedDiff(functors(diff1), functors(diff2)).hasNext()
              || iterSortedDiff(functors(diff2), functors(diff1)).hasNext()) {
        return some(AbstractionResult(NeverEqual{}));

      } else {
        return some(AbstractionResult(EqualIf().constr(diffConstr())));
      }


  } else if (_mode == Uwa::ALASCA3) {
    auto out = alasca3(*au, t1, t2);
    DEBUG_UWA(1, "alasca3", tie(t1, t2), " = ", out, " (ctxt: ", *au, " )")
    return out;

  } else if (_mode == Uwa::ALASCA4) {
    auto out = alasca4(*au, t1, t2);
    DEBUG_UWA(1, "alasca4", tie(t1, t2), " = ", out, " (ctxt: ", *au, " )")
    return out;

  } else if (_mode == Shell::Options::UnificationWithAbstraction::FUNC_EXT) {
    return funcExt(au, t1, t2);

  } else {
    auto abs = canAbstract(au, t1, t2);
    DEBUG_UWA(1, "canAbstract(", t1, ",", t2, ") = ", abs);
    return someIf(abs, [&](){
        return AbstractionResult(EqualIf().constr(UnificationConstraint(t1.clone(), t2.clone())));
    });
  }
}
void UnificationConstraintStack::add(UnificationConstraint c, Option<BacktrackData&> bd)
{ 
  if (bd) {
    backtrackablePush(_cont, std::move(c), *bd); 
  } else {
    _cont.push(std::move(c));
  }
}


UnificationConstraint UnificationConstraintStack::pop(Option<BacktrackData&> bd)
{ 
  auto old = _cont.pop();
  if (bd) {
    bd->addClosure([this, old = old.clone()]() mutable { _cont.push(std::move(old)); });
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
  return t1 == t2 
    ? Option<Literal*>()
    : Option<Literal*>(Literal::createEquality(false, t1, t2, t1.isTerm() ? SortHelper::getResultSort(t1.term()) : SortHelper::getResultSort(t2.term())));
}


}

bool AbstractingUnifier::fixedPointIteration()
{
  CALL("AbstractionResult::fixedPointIteration");
  TIME_TRACE("uwa fixedPointIteration");

  Recycled<Stack<UnificationConstraint>> todo;
  while (!constr().isEmpty()) { 
    todo->push(constr().pop(bd()));
  }

  DEBUG_FINALIZE(1, "finalizing: ", todo)
  while (!todo->isEmpty()) {
    auto c = todo->pop();
    DEBUG_FINALIZE(2, "popped: ", c);
    bool progress;
    auto res = unify(c.lhs().clone(), c.rhs().clone(), progress);
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

bool AbstractingUnifier::unify(TermList term1, unsigned bank1, TermList term2, unsigned bank2)
{
  if (_uwa._mode == Shell::Options::UnificationWithAbstraction::OFF) 
    return _subs->unify(term1, bank1, term2, bank2);

  bool progress;
  return unify(TermSpec(term1, bank1), TermSpec(term2, bank2), progress);
}

bool AbstractingUnifier::unify(TermSpec t1, TermSpec t2, bool& progress)
{
  CALL("AbstractionResult::unify");
  ASS_NEQ(_uwa._mode, Shell::Options::UnificationWithAbstraction::OFF) 
  DEBUG_UNIFY(1, *this, ".unify(", t1, ",", t2, ")")
  progress = false;

  if(t1 == t2) {
    progress = true;
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnificationConstraint>> toDo;
    toDo->push(UnificationConstraint(t1.clone(), t2.clone()));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint>> encountered;

    Option<MismatchHandler::AbstractionResult> absRes;
    auto doAbstract = [&](auto& l, auto& r) -> bool
    { 
      if (absRes.isSome()) DEBUG_UNIFY(2, "uwa: ", absRes)
      absRes = _uwa.tryAbstract(this, l, r);
      if (absRes) {
        DEBUG_UNIFY(2, "abstraction result: ", absRes)
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
        // if (pair.first.isVar() && isUnbound(pair.first.varSpec()) &&
        //     pair.second.isVar() && isUnbound(pair.second.varSpec())) {
        //   toDo.push(pair);
        // } else 
        if (!encountered->find(pair)) {
          encountered->insert(pair.clone());
          toDo->push(std::move(pair));
        }
    };

    auto occurs = [this](auto& var, auto& term) {
      Recycled<Stack<TermSpec>> todo;
      todo->push(term.clone());
      while (todo->isNonEmpty()) {
        auto t = todo->pop();
        auto& dt = t.deref(&subs());
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
      auto x = toDo->pop();
      auto& dt1 = x.lhs().deref(&subs());
      auto& dt2 = x.rhs().deref(&subs());
      DEBUG_UNIFY(2, "popped: ", dt1, " = ", dt2)
      if (dt1 == dt2) {
        progress = true;

      } else if(dt1.isVar() && !occurs(dt1, dt2)) {
        progress = true;
        subs().bind(dt1.varSpec(), dt2.clone());

      } else if(dt2.isVar() && !occurs(dt2, dt1)) {
        progress = true;
        subs().bind(dt2.varSpec(), dt1.clone());

      } else if(doAbstract(dt1, dt2)) {

        ASS(absRes);
        if (absRes->is<MismatchHandler::NeverEqual>()) {
          return false;

        } else {
          ASS(absRes->is<MismatchHandler::EqualIf>())
          auto& conditions = absRes->unwrap<MismatchHandler::EqualIf>();
          auto eq = [](UnificationConstraint& c, TermSpec const& lhs, TermSpec const& rhs) 
          { 
            return (c.lhs() == lhs && c.rhs() == rhs) 
                || (c.lhs() == rhs && c.rhs() == lhs); };
          if (progress 
              || conditions.constr().size() != 1 
              || conditions.unify().size() != 0
              || !eq(conditions.constr()[0], t1, t2)
              ) {
            progress = true;
          }
          for (auto& x : conditions.unify()) {
            pushTodo(std::move(x));
          }
          for (auto& x: conditions.constr()) {
            _constr->add(std::move(x), bd());
          }
        }
        absRes.take();

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
          pushTodo(UnificationConstraint(std::move(c.first), std::move(c.second)));
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

  DEBUG_UNIFY(1, *this)
  return success;
}
