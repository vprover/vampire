/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "QE/LIRA.hpp"
#include "Debug/Assertion.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/EqHelper.hpp"

namespace QE {

// struct FloorFormula {
//
// };

using Numeral = RealConstantType;
using R = RealTraits;

enum class Connective {
  Greater, Geq, Neq, Eq,
};

class NormLit {
  TermList _term;
  Connective _connective;
  Stack<TermList> _breaks;
  NormLit(TermList term, Connective connective) : _term(term), _connective(connective) {}
public:

  auto& connective() const { return _connective; }

  auto& breaks() const 
  { 
    ASSERTION_VIOLATION
    return _breaks;
  }

  RealConstantType slope(unsigned var) const {
    return evalBottomUp<RealConstantType>(_term,
        [&](auto& orig, auto* args) {
          if (orig.isVar()) {
            if (orig.var() == var) {
              return Numeral(1);
            } else {
              return Numeral(0);
            }
          } else {
            auto f = orig.term()->functor();
            auto origArg = [&](auto i) { return orig.term()->termArg(i); };
            if (R::isMul(f)) {
              auto k = R::tryNumeral(origArg(0));
              ASS(k.isSome())
              ASS_EQ(args[0], Numeral(0))
              return k.unwrap() * std::move(args[1]);
            } else if (R::isAdd(f)) {
              return std::move(args[0]) + std::move(args[1]);
            } else if (R::isFloor(f)) {
              // TODO use new bottom up evaluation to not recurse into floors when joe-uwa-refactor landed
              return Numeral(0);
            }
          }
        });
  }
  RealConstantType const& off() const;
  RealConstantType const& per() const;
  RealConstantType const& deltaInf() const;
  TermList const& xMinusInf() const;
  TermList term() const;

  static NormLit from(Literal* lit) {
    auto l = lit->termArg(0);
    auto r = lit->termArg(1);
    if (lit->isEquality()) {
      return NormLit(R::add(l, R::minus(r)), lit->isPositive() ? Connective::Eq : Connective::Neq);
    } else {
      auto f = lit->functor();
      ASS(R::isLess(f) || R::isLeq(f) || R::isGreater(f) || R::isGeq(f))
      auto strict = R::isLess(f) || R::isGreater(f);
      auto grtr = R::isGreater(f) || R::isGeq(f);
      if (lit->isNegative()) {
        strict = !strict;
        grtr = !grtr;
      }
      return NormLit(
        grtr ? R::add(l, R::minus(r))
             : R::add(r, R::minus(l)),
        strict ? Connective::Greater : Connective::Geq
      );
    }
  }
};


class Grid {
public:
  Grid(TermList anchor, Numeral per);
  IterTraits<VirtualIterator<ElimTerm>> intersect(bool lIncl, TermList min, Numeral dist, bool rIncl);
};

bool isIneq(Connective c) {
  switch (c) {
    case Connective::Greater:
    case Connective::Geq: return true;
    case Connective::Neq:
    case Connective::Eq: return false;
  }
}

bool isInclusive(Connective c) {
  switch (c) {
    case Connective::Greater:
    case Connective::Neq: return false;
    case Connective::Eq: 
    case Connective::Geq: return true;
  }
}

TermList computeLim(TermList phi);

auto elimSet(TermList var, Literal* lit_) {
  bool incl = true;
  bool excl = !incl;
  auto lit = NormLit::from(lit_);
  auto slope = lit.slope(var.var());
  auto& breaks = lit.breaks();
  auto phi = lit.term();

  auto maybeEps = [&](auto t) { 
    switch(lit.connective()) {
      case Connective::Greater:
      case Connective::Neq: return t + Epsilon {};
      case Connective::Geq:
      case Connective::Eq: return t;
    }
  };

  return ifElseIter(
      /* if */ breaks.isEmpty(),
      [&]() {
        auto set = [](std::initializer_list<ElimTerm> x) {
          Recycled<Stack<ElimTerm>> set;
          set->init(x);
          return range(0, set->size())
              .map([set = std::move(set)](auto i) { return (*set)[i]; });
        };
        auto intersection = ElimTerm(R::mul(R::constantTl(Numeral(-1) / slope), EqHelper::replace(phi, var, R::constantTl(0))));
        switch (lit.connective()) {
          case Connective::Greater: 
          case Connective::Geq:
            if (slope > RealConstantType(0)) {
              return set({ maybeEps(intersection), });
            } else {
              return set({ ElimTerm::minusInfinity(), });
            }
          case Connective::Neq:
            return set({ ElimTerm::minusInfinity(), intersection + Epsilon {} });
          case Connective::Eq:
            return set({ intersection });
        }
      },
      /* else */ 
      [&](){
        auto off = lit.off();
        auto per = lit.per();
        auto deltaInf = lit.deltaInf(); 
        auto xMinusInf = lit.xMinusInf(); 

        auto limPhi = computeLim(phi);

        auto dlin = [slope, var, limPhi](auto b) -> TermList 
        { return R::add(R::mul(R::constantTl(-slope), b), EqHelper::replace(limPhi, var, b)); };

        auto intrestGrid = [&](bool lIncl, Grid g, bool rIncl) 
        { return g.intersect(lIncl, xMinusInf, deltaInf, rIncl); };

        auto ebreak = [&](bool lIncl, bool rIncl) {
          return ifElseIter(
              off.isZero(), [&]() { return arrayIter(breaks)    .map([&](auto b) { return ElimTerm(b) + Period(per); }); }
                          , [&]() { return arrayIter(breaks).flatMap([&](auto b) { return intrestGrid(lIncl, Grid(b, per), rIncl); }); });
        };

        auto einter = [&]() {
          ASS(!slope.isZero())
          auto inters = [&]() { return arrayIter(breaks).map([&](auto b) -> TermList { return R::mul(R::constantTl(Numeral(-1) / slope), dlin(b)); }); };
          return ifElseIter(
              /* if */ off.isZero(),
              [&]() { return inters().map([&](auto i) { return i + Period(per); });  },

              /* if */ !off.isZero() && off != slope,
              [&]() { return inters().flatMap([&](auto i) { return intrestGrid(excl, Grid(i, (Numeral(1) - off/slope) * per), excl); }); },

              /* else */
              [&]() { 
                ASS(!off.isZero() && off == slope)
                return inters().map([](auto x) { return ElimTerm(x); }); }
              );
        };

        auto einf = ifElseIter((isIneq(lit.connective()) && off < Numeral(0)) 
                             || lit.connective() == Connective::Neq,
                             []() { return getSingletonIterator(ElimTerm::minusInfinity()); },
                             []() { return arrayIter(Stack<ElimTerm>()); });

        auto eseg = ifElseIter(
                      /* if */ slope.isZero() || (slope < Numeral(0) && isIneq(lit.connective()))
                    , [&]() { return ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }); }

                    , /* if */ slope > Numeral(0) && isIneq(lit.connective())
                    , [&]() { return concatIters(
                                           ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }),
                                           einter().map([&](auto i) { return maybeEps(i); })
                                     ); }

                    , /* if */ lit.connective() == Connective::Eq
                    , [&]() { ASS(!slope.isZero())
                              return einter(); }

                    // else
                    , [&]() { ASS(lit.connective() == Connective::Neq && !slope.isZero())
                              return concatIters(ebreak(incl, excl), einter()).map([](auto b) { return b + Epsilon{}; }); }

            );
        return concatIters( ebreak(incl, incl), eseg, einf);
      });
}

Stack<ElimSet> LIRA::computeElimSet(unsigned var, Stack<Literal*> const& conjunction) 
{ 
  return {
    ElimSet::fromIter(
                arrayIter(conjunction)
                  .flatMap([&](auto lit) { return elimSet(TermList::var(var), lit); })
        )
  };
  // return {
  //   ElimSet<>{}
  // };
  //
  return Stack<ElimSet>(); 
}


} // namespace QE


