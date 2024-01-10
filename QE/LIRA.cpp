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
#include "Kernel/LASCA.hpp"
#include "Kernel/Term.hpp"
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
Numeral operator-(Numeral const& l, int r) { return l - Numeral(r); }
Numeral operator-(int l, Numeral const& r) { return Numeral(l) - r; }

Numeral qLcm(Numeral l, Numeral r) {
  return Numeral(IntegerConstantType::lcm(l.numerator(), r.numerator()), 
                 IntegerConstantType::gcd(l.numerator(), r.numerator()));
}

enum class Connective {
  Greater, Geq, Neq, Eq,
};

std::ostream& operator<<(std::ostream& out, Connective const& self)
{ 
  switch(self) {
    case Connective::Greater: return out << ">";
    case Connective::Geq:     return out << ">=";
    case Connective::Neq:     return out << "!=";
    case Connective::Eq:      return out << "==";
  }
} 

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
class LiraTerm {
  TermList _term;

public:
  LiraTerm(TermList term) : _term(term) {}
  TermList toNormalTerm() const { return _term; }

  template<class Res, class TargetVar, class OtherVarOrConst, class NumMul, class Add, class Floor> 
  static auto eval(TermList t, TermList var, TargetVar targetVar, OtherVarOrConst otherVarOrConst, NumMul numMul, Add add, Floor floor) {
    return evalBottomUp<Res>(t,
        [=](auto& orig, auto* args) {
          if (orig == var) {
            return targetVar();
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

  struct LiraTermSummary {
    RealConstantType slope;
    RealConstantType   off;
    RealConstantType   per;
    LinBounds  linBounds;
    TermList    lim;
    Recycled<Stack<ElimTerm>> breaks;
    friend std::ostream& operator<<(std::ostream& out, LiraTermSummary const& self)
    { return out << "LiraTermSummary {...}"; }

    TermList dist(bool plus) { return plus ? linBounds.upper() : linBounds.lower; }

    auto xMinusInf() {
      ASS(off != 0)
      return (-1 / off) * dist(off.isPositive());
    }
    auto deltaInf() {
      ASS(off != 0) 
      return (-1 / off) * linBounds.delta;
    }
  };


  LiraTermSummary summary(TermList x) const {
    return eval<LiraTermSummary>(_term, x,
        /* var x */ 
        [&]() { 
          return LiraTermSummary {
              .slope = Numeral(1),
              .off = Numeral(1),
              .per = Numeral(0),
              .linBounds = {
                .lower = R::constantTl(0),
                .delta = Numeral(0),
              },
              .lim = x,
              .breaks = Recycled<Stack<ElimTerm>>(),
          }; 
        },

        /* other var */ 
        [](TermList v) { 
          return LiraTermSummary {
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
          return LiraTermSummary {
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
          return LiraTermSummary {
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
          { return (-res.slope *  b + EqHelper::replace(t, x, b)); };

          auto breaks = [&]() {
            if (res.per == 0 &&  res.off == 0) { 
              return rstack(arrayIter(Stack<ElimTerm>())); 
            } else if (res.per == 0 && res.off != 0) {
              return rstack(getSingletonIterator((-1 / res.off) * EqHelper::replace(t, x, R::constantTl(0)) + Period(newPer)));
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

          return LiraTermSummary {
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

  template<class Var, class One, class NumMul, class Add, class Floor>
  auto match(Var var, One one, NumMul numMul, Add add, Floor floor) const -> decltype(one())  
  {
    auto tl = _term;
    if (tl.isVar()) {
      return var(tl);
    } else {
      auto term = tl.term();
      auto f = term->functor();
      if (R::isNumeral(f)) {
        return numMul(*R::tryNumeral(term), LiraTerm(R::constantTl(1)));

      } else if (R::isMul(f)) {
        auto k = R::tryNumeral(term->termArg(0));
        ASS(k.isSome())
        return numMul(*k, LiraTerm(term->termArg(1)));

      } else if (R::isMinus(f)) {
        return numMul(Numeral(-1), LiraTerm(term->termArg(0)));

      } else if (R::isAdd(f)) {
        return add(LiraTerm(term->termArg(0)), LiraTerm(term->termArg(1)));

      } else if (R::isFloor(f)) {
        return floor(LiraTerm(term->termArg(0)));

      } else {
        return var(tl);

      }
    }
  }

  friend std::ostream& operator<<(std::ostream& out, LiraTerm const& self)
  { return out << self._term; }

};

/** represents _term != epsilon */
class EpsLit {
  LiraTerm _term;
public:

  EpsLit(TermList term) 
    : _term(term) 
  {}

  LiraTerm term() const { return _term; }
};



class NormLit 
{
  LiraTerm _term;
  Connective _connective;
public:
  NormLit(TermList term, Connective connective) : _term(term), _connective(connective) {}
  // NormTerm normTerm() const { return { _term }; }

  auto& connective() const { return _connective; }
  // template<class Res, class TargetVar, class OtherVarOrConst, class NumMul, class Add, class Floor> 
  // static auto eval(TermList t, TermList var, TargetVar targetVar, OtherVarOrConst otherVarOrConst, NumMul numMul, Add add, Floor floor) {
  //   return evalBottomUp<Res>(t,
  //       [=](auto& orig, auto* args) {
  //         if (orig == var) {
  //           return targetVar();
  //         } else {
  //           auto f = orig.term()->functor();
  //           auto origArg = [=](auto i) { return orig.term()->termArg(i); };
  //           if (R::isMul(f)) {
  //             auto k = R::tryNumeral(origArg(0));
  //             ASS(k.isSome())
  //             return numMul(k.unwrap(), orig, std::move(args[1]));
  //
  //
  //           } else if (R::tryNumeral(orig)) {
  //             return numMul(R::tryNumeral(orig).unwrap(), R::constantTl(1), otherVarOrConst(R::constantTl(1)));
  //
  //           } else if (R::isMinus(f)) {
  //             return numMul(Numeral(-1), origArg(0), std::move(args[0]));
  //
  //           } else if (R::isAdd(f)) {
  //             return add(origArg(0), origArg(1), std::move(args[0]), std::move(args[1]));
  //
  //           } else if (R::isFloor(f)) {
  //             return floor(origArg(0), std::move(args[0]));
  //
  //           } else {
  //             // we can't compute the slope for non-constants as they might contain variables. 
  //             // if we'd want to do that we'd have to extend the theory and this will be surely undecidable in general.
  //             ASS_EQ(orig.term()->arity(), 0)
  //             return otherVarOrConst(orig);
  //           }
  //         }
  //       });
  // }

  // template<class Res, class One, class NumMul, class Add, class Floor> 
  // static auto evalGround(TermList t, One one, NumMul numMul, Add add, Floor floor) {
  //   return eval<Res>(t, TermList::var(0),
  //       /* var x     */ []() -> Res { ASSERTION_VIOLATION_REP("not ground") },
  //       /* other var */ [&](TermList t)  -> Res { 
  //         ASS(R::tryNumeral(t) == some(Numeral(1)))
  //         // TODO this is unnecessary work because we discard the result later
  //         return one();
  //       }, 
  //       /* k * t */ 
  //       numMul,
  //
  //       /* l + r */ 
  //       add,
  //
  //       /* floor(t) */ 
  //       floor
  //   );
  // }


  // struct LinBounds {
  //   TermList lower;
  //   Numeral delta;
  //   TermList upper() const { return lower + delta; }
  //   auto asTuple() const { return std::tie(lower, delta); }
  //   friend std::ostream& operator<<(std::ostream& out, LinBounds const& self)
  //   { return out << "[" << self.lower << " (+ " << self.delta << ") ]"; }
  //   IMPL_COMPARISONS_FROM_TUPLE(LinBounds);
  // };
  //
  // struct FloorLiteral {
  //   RealConstantType slope;
  //   RealConstantType   off;
  //   RealConstantType   per;
  //   LinBounds  linBounds;
  //   TermList    lim;
  //   Recycled<Stack<ElimTerm>> breaks;
  //   friend std::ostream& operator<<(std::ostream& out, FloorLiteral const& self)
  //   { return out << "FloorLiteral {...}"; }
  //
  //   TermList dist(bool plus) { return plus ? linBounds.upper() : linBounds.lower; }
  //
  //   auto xMinusInf() {
  //     ASS(off != 0)
  //     return (-1 / off) * dist(off.isPositive());
  //   }
  // };

  

  LiraTerm term() const { return _term; }

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
  friend std::ostream& operator<<(std::ostream& out, NormLit const& self)
  { return out << self.term() << " " << self.connective() << " 0"; }
};

class LiraLiteral : public Coproduct<NormLit, EpsLit> {
public:
  using Coproduct::Coproduct;
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


auto elimSet(TermList var, NormLit const& lit) {
  bool incl = true;
  bool excl = !incl;
  auto phi = make_shared(lit.term().summary(var));
  auto slope = phi->slope;
  auto breaksIter = [=]() {
    return range(0, phi->breaks->size())
              .map([=](auto i) { return (*phi->breaks)[i]; });
  };
  auto term = lit.term().toNormalTerm();

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
        auto intersection = [&]() { return ElimTerm((-1 / slope) * EqHelper::replace(term, var, R::constantTl(0)));};
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
        { return -slope * b + EqHelper::replace(limPhi, var, b); };

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

template<class T>
using DummyIter = IterTraits<VirtualIterator<T>>;

auto elimSet(TermList var, Stack<NormLit> const& lits) 
{ return arrayIter(lits).flatMap([var](auto l) { return elimSet(var, l); }); }

auto elimSet(unsigned var, Literal* lit_) {
  auto l = NormLit::from(lit_);
  return elimSet(TermList::var(var), l);
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

namespace CDVS {
struct CDVSFormula;

struct Conjunction {
  std::shared_ptr<CDVSFormula> lhs;
  std::shared_ptr<CDVSFormula> rhs;
};

struct Disjunction {
  std::shared_ptr<CDVSFormula> lhs;
  std::shared_ptr<CDVSFormula> rhs;
};

struct Negation {
  std::shared_ptr<CDVSFormula> inner;
};

struct CDVSFormula
  : public Coproduct< NormLit
                    , Conjunction>
{

};

// Numeral simplGround(TermList t) {
//   return NormLit::evalGround<Numeral>(t, 
//       /* 1        */ [&]() { return Numeral(1); },
//       /* k * t    */ [&](auto k, auto t, auto tRes) { return k * tRes; },
//       /* l + r    */ [&](auto l, auto r, auto lRes, auto rRes) { return lRes + rRes; },
//       /* floor(t) */ [&](auto t, auto tRes) { return tRes.floor(); });
// }
//
// bool simplGround(NormLit lit) {
//   Numeral v = simplGround(lit.term());
//   switch (lit.connective()) {
//     case Connective::Greater: return v >  0;
//     case Connective::Geq:     return v >= 0;
//     case Connective::Neq:     return v != 0;
//     case Connective::Eq:      return v == 0;
//   }
//
// }

struct Assignment {
  TermList var;
  ElimTerm val;

  Assignment(TermList var, ElimTerm val)
    : var(var)
    , val(val)
  {}

  friend std::ostream& operator<<(std::ostream& out, Assignment const& self)
  { return out << self.var << " -> " << self.val; }
};

class Assignments {
  Stack<Assignment> _asgn;
public:
  Assignments() : _asgn() {}
  void push(Assignment a) { _asgn.push(std::move(a)); }
  Assignment pop() { return _asgn.pop(); }
  auto iter() const 
  { return arrayIter(_asgn); }

  friend std::ostream& operator<<(std::ostream& out, Assignments const& self)
  { return out << self._asgn; }
};
struct NfFormula;
struct Conj 
{
  std::shared_ptr<NfFormula> lhs;
  std::shared_ptr<NfFormula> rhs;
};

struct Disj 
{
  std::shared_ptr<NfFormula> lhs;
  std::shared_ptr<NfFormula> rhs;
};

struct NfFormula 
  : public Coproduct<LiraLiteral, Conj, Disj> 
{
    using Coproduct::Coproduct;

    static NfFormula top() { return NfFormula(LiraLiteral(NormLit(R::constantTl(0), Connective::Eq))); }
    static NfFormula bot() { return NfFormula(LiraLiteral(NormLit(R::constantTl(0), Connective::Neq))); }
};

class NfFormulaIter {
  Recycled<Stack<LiraLiteral>> _lits;
  void fill(NfFormula const& phi) 
  {
    return phi.match(
        [&](LiraLiteral const& l) { return _lits->push(l); },
        [&](Conj const& c) { fill(*c.lhs); fill(*c.rhs); },
        [&](Disj const& c) { fill(*c.lhs); fill(*c.rhs); });
  }

public:
  NfFormulaIter(NfFormula const& phi) 
    : _lits() 
  {
    fill(phi);
  }

  DECL_ELEMENT_TYPE(LiraLiteral);

  LiraLiteral next() { return _lits->pop(); }
  bool hasNext() { return _lits->isNonEmpty(); }
};

auto iterNormLits(NfFormula const& phi) {
  return iterTraits(NfFormulaIter(phi))
    .map([](auto l) { return l.template as<NormLit>().unwrap(); });
}

auto elimSet(TermList var, NfFormula const& phi) {
  return iterNormLits(phi)
    .flatMap([&](auto lit) { return elimSet(var, lit); })
    .flatMap([&](auto t_) {
        auto t = t_.asFinite().unwrap();
        // return getSingletonIterator(t_);
        return ifElseIter(t.period().isNone()
            , [=]() { return getSingletonIterator(t_); }
            , [=]() { 
              auto p = t.period().unwrap();
              auto eps = t.epsilon();
              auto bigPeriod = iterNormLits(phi)
                .map([=](auto l) { return l.term().summary(var).per; })
                .fold([=](auto l, auto r) { return qLcm(l,r); })
                .unwrap();

              return iterNormLits(phi)
                .flatMap([=](auto l) { 
                    auto phi = l.term().summary(var);
                    return Grid(t)
                      .intersect(true, phi.xMinusInf(), bigPeriod + phi.deltaInf(), true); })
                      .map([=](auto t2) { return ElimTerm(FiniteElimTerm(t2, eps, {})); })
                          ;
                }
            );
    });
}



#define BIN_OP(op, Class)                                                                 \
  NfFormula operator op(std::shared_ptr<NfFormula> const& lhs, std::shared_ptr<NfFormula> const& rhs) \
  { return NfFormula(Class { lhs, rhs, }); }                                              \
                                                                                          \
  NfFormula operator op(NfFormula const& lhs, std::shared_ptr<NfFormula> const& rhs)      \
  { return make_shared(lhs)  op rhs; }                                                    \
                                                                                          \
  NfFormula operator op(std::shared_ptr<NfFormula> const& lhs, NfFormula const& rhs)      \
  { return lhs  op make_shared(rhs); }                                                    \
                                                                                          \
  NfFormula operator op(NfFormula const& lhs, NfFormula const& rhs)                       \
  { return lhs  op make_shared(rhs); }                                                    \

BIN_OP(&&, Conj)
BIN_OP(||, Disj)

Option<Numeral> trivEval(LiraTerm const& phi)
{
  return phi.match(
        [&](TermList var) -> Option<Numeral> { return {}; }
      , [&]() { return some(Numeral(1)); }
      , [&](Numeral k, LiraTerm t) { 
          return k == 0 ? some(Numeral(0)) 
                        : trivEval(t).map([&](auto n) { return k * n; }); 
        }
      , [&](LiraTerm lhs, LiraTerm rhs) { 
          auto l = trivEval(lhs);
          if (l.isNone()) return l;
          auto r = trivEval(rhs);
          if (r.isNone()) return r;
          return some(*l + *r);
        }      
      , [&](LiraTerm t) { 
          return trivEval(t).map([](auto n) { return n.floor(); });
      });
}

Option<bool> trivEval(NormLit const& phi) {
  return trivEval(phi.term())
    .map([&](Numeral const& n) {
        switch (phi.connective()) {
          case Connective::Greater: return n >  0;
          case Connective::Geq:     return n >= 0;
          case Connective::Neq:     return n != 0;
          case Connective::Eq:      return n == 0;
        }});
}

NfFormula vsubs(NormLit const& phi, TermList var, FiniteElimTerm const& val) 
{
  ASS(val.period().isNone())

  if (val.epsilon().isNone())  {
    return NfFormula(LiraLiteral(NormLit(EqHelper::replace(phi.term().toNormalTerm(), var, val.term()), phi.connective())));
  } else {
    auto sum = phi.term().summary(var);
    auto limSubs = [&]() { return EqHelper::replace(sum.lim, var, val.term()); };
    if (isIneq(phi.connective()))  {
      return NfFormula(LiraLiteral(NormLit(limSubs()
                          , sum.slope >  0 ? Connective::Geq 
                          : sum.slope == 0 ? phi.connective()
                          :                  Connective::Greater)));
    } else {
      return NfFormula(LiraLiteral(NormLit(sum.slope == 0 ? limSubs()         // <- (~) lim[t] = 0
                                              : R::constantTl(1), // <- (~) 1 = 0
                                              phi.connective())));
    }

  }
}


NfFormula vsubs(EpsLit const& lit, TermList var, FiniteElimTerm const& val)
{ 
  auto phi = lit.term();
  ASS(val.period().isNone())
  if (val.epsilon()) {
    auto sum = phi.summary(var);
    auto limT = EqHelper::replace(sum.lim, var, val.term());
    return NfFormula(
        sum.slope == 1 ? LiraLiteral(NormLit(limT, Connective::Neq))
                       : LiraLiteral(EpsLit((1 / (1 - sum.slope)) * limT)));
  } else {
    /* phi[x//t] !~ eps => phi[x/t] !~ eps */ 
    return NfFormula(LiraLiteral(EpsLit(EqHelper::replace(phi.toNormalTerm(), var, val.term()))));
  }
}

NfFormula vsubs(LiraLiteral const& phi, TermList var, FiniteElimTerm const& val) 
{ return phi.apply([&](auto l) { return vsubs(l, var, val); }); }

NfFormula vsubs(NfFormula const& phi, TermList var, FiniteElimTerm const& val)
{
  ASS(val.period().isNone())

  return phi.match(
      [&](LiraLiteral const& l) { return vsubs(l, var, val); },
      [&](Conj const& c) { return vsubs(*c.lhs, var, val) && vsubs(*c.rhs,var,val); },
      [&](Disj const& c) { return vsubs(*c.lhs, var, val) || vsubs(*c.rhs,var,val); });
}


NfFormula vsubs(NfFormula const& phi, TermList var, ElimTerm val)
{ return vsubs(phi, var, *val.asFinite()); }

NfFormula vsubs(NfFormula const& phi, Assignments const& asgn) {
  auto res = phi;
  for (auto a : asgn.iter()) {
    res = vsubs(std::move(res), a.var, a.val);
  }
  return res;
}


Option<bool> trivEval(EpsLit const& phi)
{
  auto t = trivEval(phi.term());
  return someIf(t.isSome(), []() { return true; });
}

Option<bool> trivEval(LiraLiteral const& phi) 
{ return phi.apply([&](auto l) { return trivEval(l); }); }

Option<bool> trivEval(NfFormula const& phi) {
  return phi.match(
      [&](LiraLiteral const& l) { return trivEval(l); },
      [&](Conj const& c) -> Option<bool> {
        auto l = trivEval(*c.lhs);
        auto r = trivEval(*c.lhs);
        if (l.isSome()) {
          return false == *l ? some(false) : r;
        } else if (r.isSome()) {
          return false == *r ? some(false) : l;
        } else {
          ASS(l.isNone() && r.isNone())
          return {};
        }
      },
      [&](Disj const& c) -> Option<bool> {
        auto l = trivEval(*c.lhs);
        auto r = trivEval(*c.lhs);
        if (l.isSome()) {
          return true == *l ? some(true) : r;
        } else if (r.isSome()) {
          return true == *r ? some(true) : l;
        } else {
          ASS(l.isNone() && r.isNone())
          return {};
        }
      });
}

bool _decide(Stack<TermList> vars, Stack<NormLit> const& lits) 
{

  Assignments assignment;
  Stack<std::shared_ptr<NfFormula>> phi_hist;
  if (lits.isEmpty()) return true;
  phi_hist.push(make_shared(arrayIter(lits)
      .map([](auto l) { return LiraLiteral(l); })
      .map([](auto l) { return NfFormula(l); })
      .fold([](auto l, auto r) { return l && r; })
      .unwrap()));
  Stack<std::shared_ptr<NfFormula>> lemma_hist;
  lemma_hist.push(make_shared(NfFormula::top()));
  auto learn = [&]() -> NfFormula {
    DBGE(assignment);
    ASSERTION_VIOLATION_REP("TODO")};

  do {
    auto triv = trivEval(phi_hist.top() && lemma_hist.top());
    if (triv.isSome()) {
      if (*triv) {
        return true;
      } else {
        auto lemma = make_shared(learn());
        while (triv.isSome()) {
          lemma_hist.pop();
          phi_hist.pop();
          vars.push(assignment.pop().var);
          triv = trivEval(phi_hist.top() && lemma_hist.top());
          ASS_REP(triv != some(true), "assigning less variables cannot make the formula true")
        }
        for (auto& p : lemma_hist) {
          p = make_shared(p && lemma);
        }
      }
    }
    ASS_REP(vars.isNonEmpty(), outputToString("unexpeced unbound variables in ", lits))
    auto var = vars.pop();
    Option<ElimTerm> val;
    for (auto t : elimSet(var, *phi_hist.top())) {
      auto phiS = make_shared(vsubs(*phi_hist.top(), var, t));
      auto lemmaS = make_shared(vsubs(*lemma_hist.top(), var, t));
      auto triv = trivEval(phiS && lemmaS);
      if (triv != some(false)) {
        phi_hist.push(phiS);
        lemma_hist.push(lemmaS);
        val = some(t);
        break;
      }
    }

    if (val.isNone()) {
      // var cannot be assigned to any value, formula is unsat
      return false;
    } else {
      assignment.push(Assignment(var, *val));
    }
  } while(true);
}

bool ConflictDrivenVirtualSubstitution::decide(Stack<Literal*> lits) 
{
  auto vars = arrayIter(lits)
    .flatMap([](auto lit) { return VariableIterator(lit); })
    .template collect<Stack>()
    .sorted()
    .deduped();
  auto ls = arrayIter(lits).map([](auto l) { return NormLit::from(l); }).template collect<Stack>();
  return _decide(vars, ls);
}

} // namespace CDVS

} // namespace QE


