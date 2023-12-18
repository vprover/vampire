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
#include "Lib/Reflection.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/EqHelper.hpp"
#include "Lib/Reflection.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include <iterator>

namespace QE {

using Numeral = RealConstantType;
using R = RealTraits;

Numeral qLcm(Numeral l, Numeral r) {
  return Numeral(IntegerConstantType::lcm(l.numerator(), r.numerator()), 
                 IntegerConstantType::gcd(l.numerator(), r.numerator()));
}
enum class Connective {
  Greater, Geq, Neq, Eq,
};

template<class T, class... Ts>
Recycled<Stack<T>> rstack(T t, Ts... ts) 
{
  Recycled<Stack<T>> out;
  out->init({std::move(t), std::move(ts)...});
  return out;
}

TermList genQuot(TermList t, Numeral q)
{ return R::floor(R::mul(R::constantTl(Numeral(1)/q), t)); }

TermList genRem(TermList t, Numeral q)
{ return R::add(t, R::mul(R::constantTl(-q), genQuot(t,q))); }

class Grid {
  TermList _anchor;
  Numeral _per;
public:
  TermList perCeiling(TermList t) 
  { return R::add(t, genRem(R::add(_anchor, R::minus(t)), _per)); }

  TermList perFloor(TermList t) 
  { return R::add(t, R::minus(genRem(R::add(t, R::minus(_anchor)), _per))); }

  Grid(TermList anchor, Numeral per) : _anchor(anchor), _per(std::move(per)) { ASS(_per > Numeral(0)) }
  auto intersect(bool lIncl, TermList min, Numeral dist, bool rIncl) {
    auto start = lIncl ? perCeiling(min) : perFloor(R::add(min, R::constantTl(_per)));
    return natIter<Numeral>()
      .takeWhile([=](auto n) { return rIncl ? n * _per <= dist : n * _per < dist;  })
      .map([=](auto n) -> TermList { return R::add(start, R::constantTl(n * _per)); });
  }
};

TermList operator*(Numeral k, TermList t) { return R::mul(R::constantTl(k), t); }

TermList operator+(TermList s, TermList t) { return R::add(s, t); }
TermList operator-(TermList s, TermList t) { return R::add(s, R::minus(t)); }

TermList operator+(Numeral s, TermList t) { return R::constantTl(s) + t; }
TermList operator+(TermList s, Numeral t) { return s + R::constantTl(t); }
TermList operator-(Numeral s, TermList t) { return R::constantTl(s) - t; }
TermList operator-(TermList s, Numeral t) { return s - R::constantTl(t); }

TermList operator+(int s, TermList t) { return Numeral(s) + t; }
TermList operator+(TermList s, int t) { return s + Numeral(t); }
TermList operator-(int s, TermList t) { return Numeral(s) - t; }
TermList operator-(TermList s, int t) { return s - Numeral(t); }
TermList operator-(TermList s) { return R::minus(s); }

class NormLit {
  TermList _term;
  Connective _connective;
  NormLit(TermList term, Connective connective) : _term(term), _connective(connective) {}
public:

  auto& connective() const { return _connective; }


  template<class Res, class TargetVar, class OtherVarOrConst, class NumMul, class Add, class Floor> 
  static auto eval(TermList t, unsigned var, TargetVar targetVar, OtherVarOrConst otherVarOrConst, NumMul numMul, Add add, Floor floor) {
    return evalBottomUp<Res>(t,
        [=](auto& orig, auto* args) {
          if (orig.isVar()) {
            if (orig.var() == var) {
              return targetVar();
            } else {
              return otherVarOrConst(orig);
            }
          } else {
            auto f = orig.term()->functor();
            auto origArg = [=](auto i) { return orig.term()->termArg(i); };
            if (R::isMul(f)) {
              auto k = R::tryNumeral(origArg(0));
              ASS(k.isSome())
              return numMul(k.unwrap(), orig, std::move(args[1]));

            } else if (R::isMinus(f)) {
              return numMul(Numeral(-1), origArg(0), std::move(args[0]));

            } else if (R::isAdd(f)) {
              return add(origArg(0), origArg(1), std::move(args[0]), std::move(args[1]));

            } else if (R::isFloor(f)) {
              return floor(origArg(0), std::move(args[0]));

            } else {
              // we can't compute the slope for non-constants as they might contain variables. 
              // if we'd want to do that we'd have to extend the theory and this will be surely undecidable in general.
              ASS_EQ(orig.term()->arity(), 0)
              return otherVarOrConst(orig);
            }
          }
        });
  }

  struct XInfRegion {
    TermList lower;
    Numeral dist;
    TermList upper() const { return lower + dist; }
    auto asTuple() const { return std::tie(lower, dist); }
    friend std::ostream& operator<<(std::ostream& out, XInfRegion const& self)
    { return out << "[" << self.lower << " (+ " << self.dist << ") ]"; }
    IMPL_COMPARISONS_FROM_TUPLE(XInfRegion);
  };

  struct Summary {
    RealConstantType slope;
    RealConstantType   off;
    RealConstantType   per;
    XInfRegion  xInfRegion;
    TermList    lim;
    Recycled<Stack<TermList>> breaks;
    friend std::ostream& operator<<(std::ostream& out, Summary const& self)
    { return out << "Summary {...}"; }

    TermList dist(bool plus) { return plus ? xInfRegion.upper() : xInfRegion.lower; }

    auto xMinusInf() {
      ASS(!off.isZero())
      return (-1 / off) * dist(off.isPositive());
    }
  };

  Summary summary(unsigned x) {
    return eval<Summary>(_term, x,
        /* var x */ 
        [&]() { 
          return Summary {
              .slope = Numeral(1),
              .off = Numeral(1),
              .per = Numeral(0),
              .xInfRegion = {
                .lower = R::constantTl(0),
                .dist = Numeral(0),
              },
              .lim = TermList::var(x),
              .breaks = Recycled<Stack<TermList>>(),
          }; 
        },

        /* other var */ 
        [](TermList v) { 
          return Summary {
              .slope = Numeral(0),
              .off = Numeral(0),
              .per = Numeral(0),
              .xInfRegion = {
                .lower = v,
                .dist = Numeral(0),
              },
              .lim = v,
              .breaks = Recycled<Stack<TermList>>(),
          }; 
        },

        /* k * t */ 
        [](auto k, auto t, auto res) { 
          return Summary {
              .slope = k * res.slope,
              .off = k * res.off,
              .per = std::move(res.per),
              .xInfRegion = 
                k == Numeral(0) ? XInfRegion {
                    .lower = R::constantTl(0),
                    .dist = Numeral(0),
                  }
                : k > Numeral(0) ? XInfRegion {
                  .lower = k * res.xInfRegion.lower, 
                  .dist = k * res.xInfRegion.dist 
                }
                : /* k < 0 */ XInfRegion {
                  .lower = k.abs() * res.xInfRegion.upper(), 
                  .dist = k.abs() * res.xInfRegion.dist 
                }
              ,
              .lim = k * res.lim,
              .breaks = std::move(res.breaks),
          }; 
        },

        /* l + r */ 
        [](auto l, auto r, auto lRes, auto rRes) { 
          auto merge = [](auto& l, auto& r) {
            l->loadFromIterator(arrayIter(*r));
            return std::move(l);
          };
          return Summary {
              .slope = lRes.slope + rRes.slope,
              .off = lRes.off + rRes.off,
              .per = lRes.per.isZero() ? rRes.per
                   : rRes.per.isZero() ? lRes.per
                   : qLcm(lRes.per, rRes.per),
              .xInfRegion = {
                .lower = lRes.xInfRegion.lower + rRes.xInfRegion.lower, 
                .dist = lRes.xInfRegion.dist + rRes.xInfRegion.dist, 
              },
              .lim = lRes.lim + rRes.lim,
              .breaks = lRes.breaks->size() >= rRes.breaks->size() 
                   ?  merge(lRes.breaks, rRes.breaks)
                   :  merge(rRes.breaks, lRes.breaks),
          }; 
        },

        /* floor(t) */ 
        [&](auto t, auto res) { 
          auto newPer = 
                     res.off.isZero() ? Numeral(0)
                   : res.per.isZero() ? Numeral(1) / res.off
                                      : Numeral(1) / (res.off * res.per);
          auto br0 = [&]() 
          { return arrayIter(*res.breaks)
              .flatMap([&](auto b) { return Grid(b, res.per).intersect(/*incl*/ true, R::constantTl(0), newPer, /* incl */ false); }); };

          auto rstack = [](auto iter) {
            Recycled<Stack<TermList>> out;
            out->loadFromIterator(iter);
            return out;
          };
          // TODO here can be improved by heuristics
          auto maxDist = res.per;

          // TODO move this to right place. Also maybe make (non-)recursive?
          auto dlin = [&](auto b) -> TermList 
          { return (-res.slope *  b + EqHelper::replace(t, TermList::var(x), b)); };

          return Summary {
              .slope = Numeral(0),
              .off = res.off,
              .per = newPer,
              .xInfRegion = {
                .lower = res.xInfRegion.lower + -res.off, 
                .dist = res.xInfRegion.dist + res.off, 
              },
              .lim = res.slope >= 0 ? R::floor(res.lim) : -R::floor(-res.lim) - 1,
              .breaks = 
                   res.per.isZero() &&  res.off.isZero()   ? rstack(arrayIter(Stack<TermList>()))
                :  res.per.isZero() && !res.off.isZero()   ? rstack(getSingletonIterator((-1 / res.off) * EqHelper::replace(t, TermList::var(x), R::constantTl(0))))
                : !res.per.isZero() && res.slope.isZero() ? rstack(br0())
                : /* !res.per.isZero() && !res.slope.isZero() */ rstack(concatIters(
                      br0(),
                      br0()
                      .flatMap([&](auto b){ return Grid((-1 / res.slope) * dlin(b), 1 / res.slope).intersect(/* incl */ false, b, maxDist,  /* incl */ false); })
                      ))
          }; 
        }
    );
  }

  TermList term() const { return _term; }

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


auto elimSet(TermList var, Literal* lit_) {
  bool incl = true;
  bool excl = !incl;
  auto lit = NormLit::from(lit_);
  auto summary = make_shared(lit.summary(var.var()));
  auto slope = std::move(summary->slope);
  // auto breaks = make_shared(std::move(summary->breaks));
  auto breaksIter = [=]() { 
    return range(0, summary->breaks->size())
              .map([=](auto i) { return (*summary->breaks)[i]; });
  };
  auto phi = lit.term();

  auto maybeEps = [=](auto t) { 
    switch(lit.connective()) {
      case Connective::Greater:
      case Connective::Neq: return t + Epsilon {};
      case Connective::Geq:
      case Connective::Eq: return t;
    }
  };

  return ifElseIter(
      /* if */ summary->breaks->isEmpty(),
      [=]() {
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
      [=](){
        auto off = summary->off;
        auto per = summary->per;
        auto deltaInf = (*summary).xInfRegion.dist;
        auto xMinusInf = [=]() { return summary->xMinusInf(); };

        auto limPhi = summary->lim;

        auto dlin = [slope, var, limPhi](auto b) -> TermList 
        { return R::add(R::mul(R::constantTl(-slope), b), EqHelper::replace(limPhi, var, b)); };

        auto intrestGrid = [=](bool lIncl, Grid g, bool rIncl) 
        { return g.intersect(lIncl, xMinusInf(), deltaInf, rIncl).map([](TermList t) { return ElimTerm(t); }); };

        auto ebreak = [=](bool lIncl, bool rIncl) {
          return ifElseIter(
              off.isZero(), [=]() { return breaksIter().map([=](auto b) { return ElimTerm(b) + Period(per); }); }
                          , [=]() { return breaksIter().flatMap([=](auto b) { return intrestGrid(lIncl, Grid(b, per), rIncl); }); });
        };

        auto einter = [=]() {
          ASS(!slope.isZero())
          auto inters = [=]() { return breaksIter().map([=](auto b) -> TermList { return R::mul(R::constantTl(Numeral(-1) / slope), dlin(b)); }); };
          return ifElseIter(
              /* if */ off.isZero(),
              [=]() { return inters().map([=](auto i) { return i + Period(per); });  },

              /* if */ !off.isZero() && off != slope,
              [=]() { return inters().flatMap([=](auto i) { return intrestGrid(excl, Grid(i, (Numeral(1) - off/slope) * per), excl); }); },

              /* else */
              [=]() { 
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
                    , [=]() { return ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }); }

                    , /* if */ slope > Numeral(0) && isIneq(lit.connective())
                    , [=]() { return concatIters(
                                           ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }),
                                           einter().map([=](auto i) { return maybeEps(i); })
                                     ); }

                    , /* if */ lit.connective() == Connective::Eq
                    , [=]() { ASS(!slope.isZero())
                              return einter(); }

                    // else
                    , [=]() { ASS(lit.connective() == Connective::Neq && !slope.isZero())
                              return concatIters(ebreak(incl, excl), einter()).map([](auto b) { return b + Epsilon{}; }); }

            );
        return concatIters( ebreak(incl, incl), eseg, einf);
        // return concatIters( ebreak(incl, incl));
      });
}

Stack<ElimSet> LIRA::computeElimSet(unsigned var, Stack<Literal*> const& conjunction) 
{ 
  return {
    ElimSet::fromIter(
                arrayIter(conjunction)
                  .flatMap([=](auto lit) { return elimSet(TermList::var(var), lit); })
        )
  };
  // return {
  //   ElimSet<>{}
  // };
  //
  return Stack<ElimSet>(); 
}


} // namespace QE


