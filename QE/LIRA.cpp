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

namespace QE {

// struct FloorFormula {
//
// };

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
      .takeWhile([&](auto n) { return rIncl ? n * _per <= dist : n * _per < dist;  })
      .map([&](auto n) -> TermList { return R::add(start, R::constantTl(n * _per)); });
  }
};


class NormLit {
  TermList _term;
  Connective _connective;
  NormLit(TermList term, Connective connective) : _term(term), _connective(connective) {}
public:

  auto& connective() const { return _connective; }


  template<class Res, class TargetVar, class OtherVarOrConst, class NumMul, class Add, class Floor> 
  static auto eval(TermList t, unsigned var, TargetVar targetVar, OtherVarOrConst otherVarOrConst, NumMul numMul, Add add, Floor floor) {
    return evalBottomUp<Res>(t,
        [&](auto& orig, auto* args) {
          if (orig.isVar()) {
            if (orig.var() == var) {
              return targetVar();
            } else {
              return otherVarOrConst(orig);
            }
          } else {
            auto f = orig.term()->functor();
            auto origArg = [&](auto i) { return orig.term()->termArg(i); };
            if (R::isMul(f)) {
              auto k = R::tryNumeral(origArg(0));
              ASS(k.isSome())
              return numMul(k.unwrap(), orig, std::move(args[1]));

            } else if (R::isMinus(f)) {
              return numMul(Numeral(-1), origArg(0), std::move(args[0]));

            } else if (R::isAdd(f)) {
              return add(origArg(0), origArg(1), std::move(args[0]), std::move(args[1]));

            } else if (R::isFloor(f)) {
              // TODO use new bottom up evaluation to not recurse into floors when joe-uwa-refactor landed
              return floor(orig, std::move(args[0]));

            } else {
              // we can't compute the slope for non-constants as they might contain variables. 
              // if we'd want to do that we'd have to extend the theory and this will be surely undecidable in general.
              ASS_EQ(orig.term()->arity(), 0)
              return otherVarOrConst(orig);
            }
          }
        });
  }

  RealConstantType slope(unsigned x) const { return      slope(_term, x); }
  RealConstantType   off(unsigned x) const { return        off(_term, x); }
  RealConstantType   per(unsigned x) const { return        per(_term, x); }
  TermList     xMinusInf(unsigned x) const { return  xMinusInf(_term, x); }
  TermList    computeLim(unsigned x) const { return computeLim(_term, x); }
  Recycled<Stack<TermList>> breaks(unsigned x) const { return breaks(_term, x); }

  static RealConstantType slope(TermList t, unsigned x) {
    return eval<RealConstantType>(t, x,
        /* var x     */ []() { return Numeral(1); },
        /* other var */ [](TermList) { return Numeral(0); },
        /* k * t     */ [](auto k, auto t, auto res) { return k * res; },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { return lRes + rRes; },
        // TODO use new bottom up evaluation to not recurse into floors when joe-uwa-refactor landed
        /* floor(t)  */ [](auto t, auto res) { return Numeral(0); }
    );
  }

  static RealConstantType off(TermList t, unsigned x) {
    return eval<RealConstantType>(t, x,
        /* var x     */ []() { return Numeral(1); },
        /* other var */ [](TermList) { return Numeral(0); },
        /* k * t     */ [](auto k, auto t, auto res) { return k * res; },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { return lRes + rRes; },
        /* floor(t)  */ [](auto t, auto res) { return std::move(res); }
    );
  }

  static RealConstantType per(TermList t, unsigned x) {
    return eval<RealConstantType>(t, x,
        /* var x     */ []() { return Numeral(0); },
        /* other var */ [](TermList) { return Numeral(0); },
        /* k * t     */ [](auto k, auto t, auto res) { return res; },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { 
                          return lRes.isZero() ? rRes
                               : rRes.isZero() ? lRes
                               : qLcm(lRes, rRes);
                          },
        /* floor(t)  */ [&](auto t, auto res) {
                          auto o = off(t, x);
                          return   o.isZero() ? Numeral(0)
                               : res.isZero() ? Numeral(1) / o
                                              : Numeral(1) / (o * res);
        }
    );
  }


  static Recycled<Stack<TermList>> breaks(TermList t, unsigned x) {
    return eval<Recycled<Stack<TermList>>>(t, x,
        /* var x     */ [&]() { return Recycled<Stack<TermList>>(); },
        /* other var */ [&](TermList v) { return Recycled<Stack<TermList>>(); },
        /* k * t     */ [](auto k, auto t, auto res) { return std::move(res); },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { 
                          auto merge = [](auto& l, auto& r) {
                            l->loadFromIterator(arrayIter(*r));
                            return std::move(l);
                          };
                          return lRes->size() >= rRes->size() 
                                   ?  merge(lRes, rRes)
                                   :  merge(rRes, lRes);
                        },
        /* floor(t)  */ [&](auto t, auto res) {
                          auto p = per(t, x);
                          auto outerP = per(R::floor(t), x);
                          auto o = off(t, x);
                          auto s = slope(t, x);
                          Recycled<Stack<TermList>> out;

                          auto br0 = [&]() 
                          { return arrayIter(*res)
                              .flatMap([&](auto b) { return Grid(b, p).intersect(/*incl*/ true, R::constantTl(0), outerP, /* incl */ false); }); };

                          if (p.isZero() &&  o.isZero()) {
                            // no breaks
                          } else if (p.isZero() && !o.isZero())  {
                            out->push(R::mul(R::constantTl(Numeral(-1) / o), EqHelper::replace(t, TermList::var(x), R::constantTl(0))));
                          } else if (!p.isZero() &&  s.isZero()) {
                            out->loadFromIterator(br0());
                          } else {
                            ASS(!p.isZero() && !s.isZero())

                            // TODO move this to right place. Also maybe make (non-)recursive?
                            auto dlin = [s, x, t](auto b) -> TermList 
                            { return R::add(R::mul(R::constantTl(-s), b), EqHelper::replace(t, TermList::var(x), b)); };

                            // TODO here can be improved by heuristics
                            auto maxDist = p;
                            out->loadFromIterator(br0());
                            out->loadFromIterator(br0()
                                .flatMap([&](auto b) { return Grid(R::mul(R::constantTl(Numeral(-1) / s), dlin(b)), Numeral(-1) / s).intersect(/* incl */ false, b, maxDist,  /* incl */ false); }));
                          }
                          return out;
                        }
    );
  }


  static TermList computeLim(TermList t, unsigned x) {
    return eval<TermList>(t, x,
        /* var x     */ [&]() { return TermList::var(x); },
        /* other var */ [&](TermList v) { return v; },
        /* k * t     */ [](auto k, auto t, auto res) { return R::mul(R::constantTl(k), res); },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { return R::add(lRes, rRes); },
        /* floor(t)  */ [&](auto t, auto res) {
                          auto s = slope(t, x);
                          return s >= Numeral(0) ? R::floor(res) : R::add(R::minus(R::floor(R::minus(res))), R::constantTl(-1));
                        }
    );
  }

  RealConstantType deltaInf(unsigned x) const { return __dist(_term, x).dist; }

  struct XInfRegion {
    TermList lower;
    Numeral dist;
    TermList upper() const { return R::add(lower, R::constantTl(dist)); }
    auto asTuple() const { return std::tie(lower, dist); }
    friend std::ostream& operator<<(std::ostream& out, XInfRegion const& self)
    { return out << "[" << self.lower << " (+ " << self.dist << ") ]"; }
    IMPL_COMPARISONS_FROM_TUPLE(XInfRegion);
  };

  static TermList dist(TermList t, unsigned x, bool plus) { auto d = __dist(t, x); return plus ? d.upper() : d.lower; }
  static XInfRegion __dist(TermList t, unsigned x) {
    return eval<XInfRegion>(t, x,
        /* var x     */ []() { return XInfRegion { .lower = R::constantTl(Numeral(0)), .dist = Numeral(0) }; },
        /* other var */ [](TermList v) { return XInfRegion { .lower = v, .dist = Numeral(0) }; },
        /* k * t     */ [](auto k, auto t, auto res) { 
                          
                          if (k == Numeral(0)) return XInfRegion { .lower = R::constantTl(Numeral(0)), .dist = Numeral(0) };
                          if (k  > Numeral(0)) return XInfRegion { .lower = R::mul(R::constantTl(k), res.lower), .dist = k * res.dist };
                          else                 return XInfRegion { .lower = R::mul(R::constantTl(k.abs()), res.upper()), .dist = k.abs() * res.dist };
                        },
        /* l + r     */ [](auto l, auto r, auto lRes, auto rRes) { 
                          return XInfRegion { .lower = R::add(lRes.lower, rRes.lower), .dist = lRes.dist + rRes.dist, };
                        },
        /* floor(t)  */ [&](auto t, auto res) {
                          auto o = off(t, x);
                          return XInfRegion { .lower = R::add(res.lower, R::constantTl(-o)) , .dist = res.dist + o, };
                        });
  }


  static TermList xMinusInf(TermList t, unsigned x) {
    auto o = off(t, x);
    ASS(!o.isZero())
    auto d = dist(t, x, o.isPositive());
    return R::mul(R::constantTl(Numeral(-1) / std::move(o)), d);
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
  auto slope = lit.slope(var.var());
  auto breaks = lit.breaks(var.var());
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
      /* if */ breaks->isEmpty(),
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
        auto off = lit.off(var.var());
        auto per = lit.per(var.var());
        auto deltaInf = lit.deltaInf(var.var()); 
        auto xMinusInf = lit.xMinusInf(var.var()); 

        auto limPhi = lit.computeLim(var.var());

        auto dlin = [slope, var, limPhi](auto b) -> TermList 
        { return R::add(R::mul(R::constantTl(-slope), b), EqHelper::replace(limPhi, var, b)); };

        auto intrestGrid = [&](bool lIncl, Grid g, bool rIncl) 
        { return g.intersect(lIncl, xMinusInf, deltaInf, rIncl).map([](TermList t) { return ElimTerm(t); }); };

        auto ebreak = [&](bool lIncl, bool rIncl) {
          return ifElseIter(
              off.isZero(), [&]() { return arrayIter(*breaks)    .map([&](auto b) { return ElimTerm(b) + Period(per); }); }
                          , [&]() { return arrayIter(*breaks).flatMap([&](auto b) { return intrestGrid(lIncl, Grid(b, per), rIncl); }); });
        };

        auto einter = [&]() {
          ASS(!slope.isZero())
          auto inters = [&]() { return arrayIter(*breaks).map([&](auto b) -> TermList { return R::mul(R::constantTl(Numeral(-1) / slope), dlin(b)); }); };
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


