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

namespace AutoSimplifyingRealOps {

  TermList operator-(TermList s) { 
    return R::isNumeral(s) ? R::constantTl(-(*R::tryNumeral(s)))
         : s.isTerm() && R::isMinus(s.term()->functor()) 
                           ? s.term()->termArg(0)
                           : R::minus(s);
  }

  TermList operator*(Numeral k, TermList t) { 
    return  k == 0 ? R::constantTl(0) 
          : k == 1 ? t
          : k == -1 ? -t
          : R::mul(R::constantTl(k), t); }

  TermList operator+(TermList s, TermList t) { 
    return R::tryNumeral(s) == some(Numeral(0)) ? t
         : R::tryNumeral(t) == some(Numeral(0)) ? s
         : R::add(s, t);
  }

  TermList operator-(TermList s, TermList t) { return s + (-t); }

  TermList operator+(Numeral s, TermList t) { return R::constantTl(s) + t; }
  TermList operator+(TermList s, Numeral t) { return s + R::constantTl(t); }
  TermList operator-(Numeral s, TermList t) { return R::constantTl(s) - t; }
  TermList operator-(TermList s, Numeral t) { return s - R::constantTl(t); }

  TermList operator+(int s, TermList t) { return Numeral(s) + t; }
  TermList operator+(TermList s, int t) { return s + Numeral(t); }
  TermList operator-(int s, TermList t) { return Numeral(s) - t; }
  TermList operator-(TermList s, int t) { return s - Numeral(t); }


}

using namespace AutoSimplifyingRealOps;

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
{ return R::floor((1/q) * t); }

TermList genRem(TermList t, Numeral q)
{ return t + -q * genQuot(t,q); }

class Grid {
  TermList _anchor;
  Numeral _per;
public:
  TermList perCeiling(TermList t) 
  { return t + genRem(_anchor - t, _per); }

  TermList perFloor(TermList t) 
  { return t - genRem(t - _anchor, _per); }

  Grid(TermList anchor, Numeral per) : _anchor(anchor), _per(std::move(per)) { ASS(_per > Numeral(0)) }
  Grid(ElimTerm t) : Grid(t.asFinite().unwrap().term(), t.asFinite().unwrap().period().unwrap().p) 
  {
    ASS(t.asFinite().unwrap().epsilon().isNone())
  }
  auto intersect(bool lIncl, TermList min, Numeral dist, bool rIncl) {
    auto start = lIncl ? perCeiling(min) : perFloor(min + _per);
    return natIter<Numeral>()
      .takeWhile([=](auto n) { return rIncl ? n * _per <= dist : n * _per < dist;  })
      .map([=](auto n) -> TermList { return start + (n * _per); });
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


            } else if (R::tryNumeral(orig)) {
              return numMul(R::tryNumeral(orig).unwrap(), R::constantTl(1), otherVarOrConst(R::constantTl(1)));

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

  struct LinBounds {
    TermList lower;
    Numeral delta;
    TermList upper() const { return lower + delta; }
    auto asTuple() const { return std::tie(lower, delta); }
    friend std::ostream& operator<<(std::ostream& out, LinBounds const& self)
    { return out << "[" << self.lower << " (+ " << self.delta << ") ]"; }
    IMPL_COMPARISONS_FROM_TUPLE(LinBounds);
  };

  struct FloorLiteral {
    RealConstantType slope;
    RealConstantType   off;
    RealConstantType   per;
    LinBounds  linBounds;
    TermList    lim;
    Recycled<Stack<ElimTerm>> breaks;
    friend std::ostream& operator<<(std::ostream& out, FloorLiteral const& self)
    { return out << "FloorLiteral {...}"; }

    TermList dist(bool plus) { return plus ? linBounds.upper() : linBounds.lower; }

    auto xMinusInf() {
      ASS(off != 0)
      return (-1 / off) * dist(off.isPositive());
    }
  };

  FloorLiteral summary(unsigned x) {
    return eval<FloorLiteral>(_term, x,
        /* var x */ 
        [&]() { 
          return FloorLiteral {
              .slope = Numeral(1),
              .off = Numeral(1),
              .per = Numeral(0),
              .linBounds = {
                .lower = R::constantTl(0),
                .delta = Numeral(0),
              },
              .lim = TermList::var(x),
              .breaks = Recycled<Stack<ElimTerm>>(),
          }; 
        },

        /* other var */ 
        [](TermList v) { 
          return FloorLiteral {
              .slope = Numeral(0),
              .off = Numeral(0),
              .per = Numeral(0),
              .linBounds = {
                .lower = v,
                .delta = Numeral(0),
              },
              .lim = v,
              .breaks = Recycled<Stack<ElimTerm>>(),
          }; 
        },

        /* k * t */ 
        [](auto k, auto t, auto res) { 
          return FloorLiteral {
              .slope = k * res.slope,
              .off = k * res.off,
              .per = std::move(res.per),
              .linBounds = 
                k == Numeral(0) ? LinBounds {
                    .lower = R::constantTl(0),
                    .delta = Numeral(0),
                  }
                : k > Numeral(0) ? LinBounds {
                  .lower = k * res.linBounds.lower, 
                  .delta = k * res.linBounds.delta 
                }
                : /* k < 0 */ LinBounds {
                  .lower = k.abs() * res.linBounds.upper(), 
                  .delta  = k.abs() * res.linBounds.delta 
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
          return FloorLiteral {
              .slope = lRes.slope + rRes.slope,
              .off = lRes.off + rRes.off,
              .per = lRes.per == 0 ? rRes.per
                   : rRes.per == 0 ? lRes.per
                   : qLcm(lRes.per, rRes.per),
              .linBounds = {
                .lower = lRes.linBounds.lower + rRes.linBounds.lower, 
                .delta = lRes.linBounds.delta + rRes.linBounds.delta, 
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
                     res.off == 0 ? Numeral(0)
                   : res.per == 0 ? 1 / res.off
                                  : 1 / (res.off * res.per);
          // auto br0 = [&]() 
          // { return arrayIter(*res.breaks)
          //     .flatMap([&](auto b) { return Grid(b, res.per).intersect(/*incl*/ true, R::constantTl(0), newPer, /* incl */ false); }); };
          //
          auto rstack = [](auto iter) {
            Recycled<Stack<ElimTerm>> out;
            out->loadFromIterator(iter);
            return out;
          };

          // TODO move this to right place. Also maybe make (non-)recursive?
          auto dlin = [&](auto b) -> TermList 
          { return (-res.slope *  b + EqHelper::replace(t, TermList::var(x), b)); };

          auto breaks = [&]() {
            if (res.per == 0 &&  res.off == 0) { 
              return rstack(arrayIter(Stack<ElimTerm>())); 
            } else if (res.per == 0 && res.off != 0) {
              return rstack(getSingletonIterator((-1 / res.off) * EqHelper::replace(t, TermList::var(x), R::constantTl(0)) + Period(newPer)));
            } else if (res.per != 0 && res.slope == 0) {
              return std::move(res.breaks);
            } else {
              ASS(res.per != 0 && res.slope != 0)
              auto pmin = arrayIter(*res.breaks).map([](auto& b) { return b.asFinite()->period()->p; }).min();
              auto out = std::move(res.breaks);
              out->loadFromIterator(arrayIter(*out)
                        .flatMap([&](ElimTerm b_plus_pZ_) { 
                          auto b_plus_pZ = b_plus_pZ_.asFinite().unwrap();
                          auto b = b_plus_pZ.term();
                          auto maxDist = pmin.unwrap();
                          return Grid((-1 / res.slope) * dlin(b), 1 / res.slope)
                                  .intersect(/* incl */ false, b, maxDist,  /* incl */ false)
                                  .map([&](auto i) -> ElimTerm { return i + Period(newPer); });
                        })
                  );
              return out;
            }
          };

          return FloorLiteral {
              .slope = Numeral(0),
              .off = res.off,
              .per = newPer,
              .linBounds = {
                .lower = res.linBounds.lower + -res.off, 
                .delta = res.linBounds.delta + res.off, 
              },
              .lim = res.slope >= 0 ? R::floor(res.lim) : -R::floor(-res.lim) - 1,
              .breaks = breaks(),
          }; 
        }
    );
  }

  TermList term() const { return _term; }

  static NormLit from(Literal* lit) {
    auto l = lit->termArg(0);
    auto r = lit->termArg(1);
    if (lit->isEquality()) {
      return NormLit(l - r, lit->isPositive() ? Connective::Eq : Connective::Neq);
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
        grtr ? l - r : r - l,
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


auto elimSet(unsigned var, Literal* lit_) {
  bool incl = true;
  bool excl = !incl;
  auto lit = NormLit::from(lit_);
  auto phi = make_shared(lit.summary(var));
  auto slope = phi->slope;
  auto breaksIter = [=]() {
    return range(0, phi->breaks->size())
              .map([=](auto i) { return (*phi->breaks)[i]; });
  };
  auto term = lit.term();

  auto maybeEps = [=](auto t) { 
    switch(lit.connective()) {
      case Connective::Greater:
      case Connective::Neq: return t + Epsilon {};
      case Connective::Geq:
      case Connective::Eq: return t;
    }
  };

  return ifElseIter(
      /* if */ phi->breaks->isEmpty(),
      [=]() {
        auto set = [](std::initializer_list<ElimTerm> x) {
          Recycled<Stack<ElimTerm>> set;
          set->init(x);
          return range(0, set->size())
              .map([set = std::move(set)](auto i) { return (*set)[i]; });
        };
        auto intersection = [&]() { return ElimTerm((-1 / slope) * EqHelper::replace(term, TermList::var(var), R::constantTl(0)));};
        switch (lit.connective()) {
          case Connective::Greater: 
          case Connective::Geq:
            if (slope > RealConstantType(0)) {
              return set({ maybeEps(intersection()), });
            } else {
              return set({ ElimTerm::minusInfinity(), });
            }
          case Connective::Neq:
            return set({ ElimTerm::minusInfinity(), intersection() + Epsilon {} });
          case Connective::Eq:
            return set({ intersection() });
        }
      },
      /* else */
      [=](){
        // using namespace OtherRealOps;

        auto off = phi->off;
        auto per = phi->per;
        auto deltaInf = phi->linBounds.delta;

        auto limPhi = phi->lim;

        auto dlin = [slope, var, limPhi](auto b) -> TermList 
        { return -slope * b + EqHelper::replace(limPhi, TermList::var(var), b); };

        auto linBounds = [=](bool lIncl, Grid g, bool rIncl) 
        { return g.intersect(lIncl, phi->xMinusInf(), deltaInf, rIncl).map([](TermList t) { return ElimTerm(t); }); };

        auto ebreak = [=](bool lIncl, bool rIncl) {
          return ifElseIter(
              off == 0, [=]() { return breaksIter(); }
                      , [=]() { return breaksIter().flatMap([=](auto b) { return linBounds(lIncl, Grid(b), rIncl); }); });
        };

        auto einter = [=]() {
          ASS(slope != 0)
          auto inter = [=](auto b) { 
            auto out = (-1 / slope) * dlin(b.asFinite()->term()); 
              return out;
          };
          return ifElseIter(
              /* if */ off == 0,
              [=]() { return breaksIter().map([=](auto b) { return inter(b) + *b.asFinite()->period(); });  },

              /* if */ off != 0 && off != slope,
              [=]() { return breaksIter().flatMap([=](auto b) { return linBounds(excl, Grid(inter(b), (Numeral(1) - (off/slope)) * b.asFinite()->period()->p), excl); }); },

              /* else */
              [=]() { 
                ASS(off != 0 && off == slope)
                return breaksIter()
                         .map([=](auto b) { return ElimTerm(inter(b)); }); }
              );
        };

        auto einf = ifElseIter((isIneq(lit.connective()) && off < 0) 
                             || lit.connective() == Connective::Neq,
                             []() { return getSingletonIterator(ElimTerm::minusInfinity()); },
                             []() { return arrayIter(Stack<ElimTerm>()); });

        auto eseg = ifElseIter(
                      /* if */ slope == 0 || (slope < 0 && isIneq(lit.connective()))
                    , [=]() { return ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }); }

                    , /* if */ slope > 0 && isIneq(lit.connective())
                    , [=]() { return concatIters(
                                           ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }),
                                           einter().map([=](auto i) { return maybeEps(i); })
                                     ); }

                    , /* if */ lit.connective() == Connective::Eq
                    , [=]() { ASS(slope != 0); return einter(); }

                    // else
                    , [=]() { ASS(lit.connective() == Connective::Neq && slope != 0)
                              return concatIters(ebreak(incl, excl), einter()).map([](auto b) { return b + Epsilon{}; }); }

            );
        return concatIters( ebreak(incl, incl), eseg, einf);
      });
}

IterTraits<VirtualIterator<ElimTerm>> LIRA::iterElimSet(unsigned var, Literal* lit)
{ return iterTraits(pvi(elimSet(var, lit))); }

Stack<ElimSet> LIRA::computeElimSet(unsigned var, Stack<Literal*> const& conjunction) 
{ 
  return {
    ElimSet::fromIter(
                arrayIter(conjunction)
                  .flatMap([=](auto lit) { return elimSet(var, lit); })
        )
  };
  return Stack<ElimSet>(); 
}


} // namespace QE


