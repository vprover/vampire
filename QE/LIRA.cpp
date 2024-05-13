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
#include "Inferences/PolynomialEvaluation.hpp"
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



using namespace AutoSimplifyingRealOps;

Numeral qLcm(Numeral l, Numeral r) {
  return Numeral(IntegerConstantType::lcm(l.numerator(), r.numerator()), 
                 IntegerConstantType::gcd(l.numerator(), r.numerator()));
}

enum class LiraPred {
  Greater, Geq, Neq, Eq,
};

std::ostream& operator<<(std::ostream& out, LiraPred const& self)
{ 
  switch(self) {
    case LiraPred::Greater: return out << ">";
    case LiraPred::Geq:     return out << ">=";
    case LiraPred::Neq:     return out << "!=";
    case LiraPred::Eq:      return out << "==";
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

  TermList perCeiling(TermList t) const
  { return t + genRem(_anchor - t, _per); }

  TermList perFloor(TermList t) const
  { return t - genRem(t - _anchor, _per); }

  Grid(TermList anchor, Numeral per) : _anchor(anchor), _per(std::move(per)) { ASS_REP(_per > Numeral(0), _per) }
  Grid(ElimTerm const& t) : Grid(t.asFinite().unwrap().term(), t.asFinite().unwrap().period().unwrap().p) 
  {
    ASS(t.asFinite().unwrap().epsilon().isNone())
  }
  auto intersect(bool lIncl, TermList min, Numeral dist, bool rIncl) const {
    ASS(dist >= 0)
    auto start = lIncl ? this->perCeiling(min) : this->perFloor(min + _per);
    auto less = [=](auto l, auto r) { return rIncl ? l <= r : l < r; };
    auto per  = this->_per;
    return natIter<Numeral>()
      .takeWhile([=](auto n) { return less(n * per, dist); })
      .map([start = std::move(start),per](auto n) -> TermList { return start + (n * per); });
  }
};

template<class T> 
T integrity(T t) {
  t.integrity();
  return t;
}

class LiraTerm 
{
  TermList _term;

public:
  LiraTerm(TermList term) 
    : _term(term) {}
  TermList toNormalTerm() const { return _term; }

  template<class Res, class TargetVar, class OtherVarOrConst, class NumMul, class Add, class Floor> 
  static auto eval(TermList t, TermList var, TargetVar targetVar, OtherVarOrConst otherVarOrConst, NumMul numMul, Add add, Floor floor) {
    return evalBottomUp<Res>(t,
        [=](auto& orig, auto* args) {
          if (orig == var) {
            return integrity(targetVar());
          } else if (orig.isVar()) {
            return integrity(otherVarOrConst(orig));
          } else {
            auto f = orig.term()->functor();
            auto origArg = [=](auto i) { return orig.term()->termArg(i); };
            if (R::isMul(f)) {
              auto k = R::tryNumeral(origArg(0));
              ASS(k.isSome())
              return integrity(numMul(k.unwrap(), origArg(1), std::move(args[1])));


            } else if (R::tryNumeral(orig)) {
              return integrity(numMul(R::tryNumeral(orig).unwrap(), R::constantTl(1), otherVarOrConst(R::constantTl(1))));

            } else if (R::isMinus(f)) {
              return integrity(numMul(Numeral(-1), origArg(0), std::move(args[0])));

            } else if (R::isAdd(f)) {
              return integrity(add(origArg(0), origArg(1), std::move(args[0]), std::move(args[1])));

            } else if (R::isFloor(f)) {
              return integrity(floor(origArg(0), std::move(args[0])));

            } else {
              // we can't compute the slope for non-constants as they might contain variables. 
              // if we'd want to do that we'd have to extend the theory and this will be surely undecidable in general.
              ASS_EQ(orig.term()->arity(), 0)
              return integrity(otherVarOrConst(orig));
            }
          }
        });
  }



  
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
                k == 0 ? LinBounds {
                    .lower = R::constantTl(0),
                    .delta = Numeral(0),
                  }
                : k > 0 ? LinBounds {
                  .lower = k * res.linBounds.lower, 
                  .delta = k * res.linBounds.delta 
                }
                : /* k < 0 */ LinBounds {
                  .lower = k * res.linBounds.lower + k * res.linBounds.delta,
                  .delta = k.abs() * res.linBounds.delta 
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
                   : res.per == 0 ? 1 / res.off.abs()
                                  : RealConstantType(RationalConstantType((res.off.abs() * res.per).numerator())) / res.off.abs();
          // auto br0 = [&]() 
          // { return arrayIter(*res.breaks)
          //     .flatMap([&](auto b) { return Grid(b, res.per).intersect(/*incl*/ true, R::constantTl(0), newPer, /* incl */ false); }); };

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
                          return Grid((-1 / res.slope) * dlin(b), (1 / res.slope).abs())
                                  .intersect(/* incl */ false, b, maxDist,  /* incl */ false)
                                  .map([&](auto i) -> ElimTerm { return i + Period(newPer); });
                        })
                  );
              return out;
            }
          };
          auto br = breaks();

          return LiraTermSummary {
              .slope = Numeral(0),
              .off = res.off,
              .per = newPer,
              .linBounds = {
                .lower = res.linBounds.lower - 1,
                .delta = res.linBounds.delta + 1, 
              },
              .lim = res.slope >= 0 ? R::floor(res.lim) : -R::floor(-res.lim) - 1,
              .breaks = std::move(br),
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

LiraTermSummary LiraTermSummary::from(TermList var, TermList term)
{ return LiraTerm(term).summary(var); }

/** represents _term != epsilon */
class EpsLit {
  LiraTerm _term;
public:

  EpsLit(TermList term) 
    : _term(term) 
  {}

  LiraTerm term() const { return _term; }
  friend std::ostream& operator<<(std::ostream& out, EpsLit const& self)
  { return out << self._term << " != " << Epsilon {}; }
};



class LiraLit 
{
  LiraTerm _term;
  LiraPred _connective;
public:
  LiraLit(TermList term, LiraPred connective) : _term(term), _connective(connective) {}

  auto& connective() const { return _connective; }
  LiraTerm term() const { return _term; }

  static LiraLit from(Literal* lit) {
    auto l = lit->termArg(0);
    auto r = lit->termArg(1);
    if (lit->isEquality()) {
      return LiraLit(l - r, lit->isPositive() ? LiraPred::Eq : LiraPred::Neq);
    } else {
      auto f = lit->functor();
      ASS(R::isLess(f) || R::isLeq(f) || R::isGreater(f) || R::isGeq(f))
      auto strict = R::isLess(f) || R::isGreater(f);
      auto grtr = R::isGreater(f) || R::isGeq(f);
      if (lit->isNegative()) {
        strict = !strict;
        grtr = !grtr;
      }
      return LiraLit(
        grtr ? l - r : r - l,
        strict ? LiraPred::Greater : LiraPred::Geq
      );
    }
  }
  friend std::ostream& operator<<(std::ostream& out, LiraLit const& self)
  { return out << self.term() << " " << self.connective() << " 0"; }
};

class LiraLiteral : public Coproduct<LiraLit, EpsLit> {
public:
  using Coproduct::Coproduct;
};

bool isIneq(LiraPred c) {
  switch (c) {
    case LiraPred::Greater:
    case LiraPred::Geq: return true;
    case LiraPred::Neq:
    case LiraPred::Eq: return false;
  }
}

bool isInclusive(LiraPred c) {
  switch (c) {
    case LiraPred::Greater:
    case LiraPred::Neq: return false;
    case LiraPred::Eq: 
    case LiraPred::Geq: return true;
  }
}

TermList simpl(TermList t) 
{ return PolynomialEvaluation::evaluate(t); }

ElimTerm simpl(ElimTerm t) 
{
  auto fin = t.asFinite();
  if (fin) {
    return ElimTerm(FiniteElimTerm(PolynomialEvaluation::evaluate(fin->term()), fin->epsilon(), fin->period()));
  } else {
    return t;
  }
}


LiraTerm simpl(LiraTerm const& t) 
{ return LiraTerm(simpl(t.toNormalTerm())); }

EpsLit simpl(EpsLit const& lit) 
{ return EpsLit(simpl(lit.term()).toNormalTerm()); }

LiraLit simpl(LiraLit const& lit) 
{ return LiraLit(simpl(lit.term()).toNormalTerm(), lit.connective()); }

LiraLiteral simpl(LiraLiteral lit) 
{ return lit.apply([&](auto l) { return LiraLiteral(simpl(l)); }); }


template<class Iter>
auto simplIter(Iter i) 
{ return iterTraits(std::move(i)).map([](auto x) { return simpl(std::move(x)); }); }


template<class Iter>
auto dbgIter(Iter iter) 
{ return iter.template collect<Stack>(); }

auto elimSet(TermList var, LiraLit const& lit) {
#define DEBUG_ELIMSET(lvl, ...) if (lvl < 2) DBG(__VA_ARGS__)
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
      case LiraPred::Greater:
      case LiraPred::Neq: return t + Epsilon {};
      case LiraPred::Geq:
      case LiraPred::Eq: return ElimTerm(t);
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
        auto phiZero = [&]() { return EqHelper::replace(term, var, R::zero()); };
        if (phi->slope == 0)  {
          return set({ ElimTerm(phiZero()) });
        }
        auto intersection = [&]() { return ElimTerm((-1 / slope) * phiZero());};
        switch (lit.connective()) {
          case LiraPred::Greater: 
          case LiraPred::Geq:
            if (slope > RealConstantType(0)) {
              return set({ maybeEps(intersection()), });
            } else {
              return set({ ElimTerm::minusInfinity(), });
            }
          case LiraPred::Neq:
            return set({ ElimTerm::minusInfinity(), intersection() + Epsilon {} });
          case LiraPred::Eq:
            return set({ intersection() });
        }
      },
      /* else */
      [=](){
        // using namespace OtherRealOps;

        auto off = phi->off;
        auto per = phi->per;
        auto deltaX = phi->linBounds.delta;

        auto limPhi = phi->lim;

        auto dlin = [slope, var, limPhi](auto b) -> TermList 
        { return -slope * b + EqHelper::replace(limPhi, var, b); };

        if (phi->off != 0) {
          DEBUG_ELIMSET(1, "lower X: ", simpl(phi->lowerX()))
          DEBUG_ELIMSET(1, "delta X: ", phi->deltaX())
        }
        

        auto linBounds = [=](bool lIncl, Grid g, bool rIncl) 
        { return g.intersect(lIncl, phi->lowerX(), deltaX, rIncl).map([](TermList t) { return ElimTerm(t); }); };

        auto ebreak = [=](bool lIncl, bool rIncl) {
          return simplIter(ifElseIter(
              off == 0, [=]() { return breaksIter(); }
                      , [=]() { return breaksIter().flatMap([=](auto b) { return linBounds(lIncl, Grid(b), rIncl); }); }))
            ;
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
              [=]() { return breaksIter().flatMap([=](auto b) { return linBounds(excl, Grid(inter(b), (1 - (off/slope)).abs() * b.asFinite()->period()->p), excl); }); },

              /* else */
              [=]() { 
                ASS(off != 0 && off == slope)
                return breaksIter()
                         .map([=](auto b) { return ElimTerm(inter(b)); }); }
              );
        };

        auto einfMinus= [=]() { return simplIter(
            ifElseIter((isIneq(lit.connective()) && off < 0) 
                             || lit.connective() == LiraPred::Neq,
                             []() { return getSingletonIterator(ElimTerm::minusInfinity()); },
                             []() { return arrayIter(Stack<ElimTerm>()); }));
        };

        auto einfPlus= [=]() { return simplIter(
            ifElseIter((isIneq(lit.connective()) && off > 0) 
                             || lit.connective() == LiraPred::Neq,
                             [=]() { return getSingletonIterator(maybeEps(phi->upperX())); },
                             []() { return arrayIter(Stack<ElimTerm>()); }));
        };

        auto eseg = [=]() { return simplIter(
            ifElseIter(
                      /* if */ slope == 0 || (slope < 0 && isIneq(lit.connective()))
                    , [=]() { return ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }); }

                    , /* if */ slope > 0 && isIneq(lit.connective())
                    , [=]() { return concatIters(
                                           ebreak(incl, excl).map([](auto b) { return b + Epsilon{}; }),
                                           einter().map([=](auto i) { return maybeEps(i); })
                                     ); }

                    , /* if */ lit.connective() == LiraPred::Eq
                    , [=]() { ASS(slope != 0); return einter(); }

                    // else
                    , [=]() { ASS(lit.connective() == LiraPred::Neq && slope != 0)
                              return concatIters(ebreak(incl, excl), einter()).map([](auto b) { return b + Epsilon{}; }); }

            )); 
        };
        DEBUG_ELIMSET(0, "ebreak: ", dbgIter(ebreak(incl,incl)))
        DEBUG_ELIMSET(0, "eseg:   ", dbgIter(eseg()))
        DEBUG_ELIMSET(0, "einf-:  ", dbgIter(einfMinus()))
        return concatIters( eseg(), ebreak(incl, incl), einfMinus(), einfPlus());
        // return concatIters( ebreak(incl, incl), eseg(), einfMinus());
      });
}

template<class T>
using DummyIter = IterTraits<VirtualIterator<T>>;

auto elimSet(TermList var, Stack<LiraLit> const& lits) 
{ return arrayIter(lits).flatMap([var](auto l) { return elimSet(var, l); }); }

auto elimSet(unsigned var, Literal* lit_) {
  auto l = LiraLit::from(lit_);
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
  : public Coproduct< LiraLit
                    , Conjunction>
{

};

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

  auto size() const { return _asgn.size(); }
  auto operator[](unsigned i)       -> decltype(auto) { return _asgn[i]; }
  auto operator[](unsigned i) const -> decltype(auto) { return _asgn[i]; }

  friend std::ostream& operator<<(std::ostream& out, Assignments const& self)
  { return out << self._asgn; }
};
struct LiraFormula;
struct Conj 
{
  std::shared_ptr<LiraFormula> lhs;
  std::shared_ptr<LiraFormula> rhs;
};

struct Disj 
{
  std::shared_ptr<LiraFormula> lhs;
  std::shared_ptr<LiraFormula> rhs;
};

struct LiraFormula 
  : public Coproduct<LiraLiteral, Conj, Disj> 
{
    using Coproduct::Coproduct;

    static LiraFormula top() { return LiraFormula(LiraLiteral(LiraLit(R::constantTl(0), LiraPred::Eq))); }
    static LiraFormula bot() { return LiraFormula(LiraLiteral(LiraLit(R::constantTl(0), LiraPred::Neq))); }
};

class LiraFormulaIter {
  Recycled<Stack<LiraLiteral>> _lits;
  void fill(LiraFormula const& phi) 
  {
    return phi.match(
        [&](LiraLiteral const& l) { return _lits->push(l); },
        [&](Conj const& c) { fill(*c.lhs); fill(*c.rhs); },
        [&](Disj const& c) { fill(*c.lhs); fill(*c.rhs); });
  }

public:
  LiraFormulaIter(LiraFormula const& phi) 
    : _lits() 
  {
    fill(phi);
  }

  DECL_ELEMENT_TYPE(LiraLiteral);

  LiraLiteral next() { return _lits->pop(); }
  bool hasNext() { return _lits->isNonEmpty(); }
};

auto iterLiraLits(LiraFormula const& phi) {
  return iterTraits(LiraFormulaIter(phi))
    .map([](auto l) { return l.template as<LiraLit>().unwrap(); });
}

template<class Iter>
auto flattenPeriods(TermList var, Stack<LiraLit> const& lits_, Iter elimTerms) {
  auto lits = &lits_;
  return iterTraits(std::move(elimTerms))
    .flatMap([=](auto t_) {
        auto t = t_.asFinite().unwrap();
        // return getSingletonIterator(t_);
        return ifElseIter(t.period().isNone()
            , [=]() { return getSingletonIterator(t_); }
            , [=]() { 
              auto p = t.period().unwrap();
              auto eps = t.epsilon();
              auto bigPeriod = arrayIter(*lits)
                .map([=](auto l) { return l.term().summary(var); })
                // .filter([](auto& l) { return l.off != 0; })
                .map([=](auto l) { return l.per; })
                .filter([](auto p) { return p != 0; })
                .fold([=](auto l, auto r) { return qLcm(l,r); })
                // .unwrap();
                || Numeral(0);
                // .unwrap(); // TODO check whether this matches up with theory part

              auto aperiodicLits = [=]() { 
                return arrayIter(*lits)
                  .map([=](auto l) { return l.term().summary(var); })
                  .filter([](auto& phi) { return phi.off != 0; }); 
              };
              auto intervals = ifElseIter(aperiodicLits().hasNext(),
                  [=]() { return aperiodicLits()
                                   .map([=](auto phi) { return make_pair(phi.lowerX(), bigPeriod + phi.deltaX()); }); },
                  [=]() { return getSingletonIterator(make_pair(R::zero(), bigPeriod)); });

              return intervals
                .flatMap([=](auto inter) { 
                    // auto phi = l.term().summary(var);
                    return Grid(t.term(), p.p)
                      .intersect(true, inter.first, inter.second, true); })
                      .map([=](auto t2) { return ElimTerm(FiniteElimTerm(t2, eps, {})); })
                          ;
              }
            );
    });
}

// auto elimSet(TermList var, LiraFormula const& phi) {
//   return iterLiraLits(phi)
//     .flatMap([&](auto lit) { return elimSet(var, lit); })
//     .flatMap([&](auto t_) {
//         auto t = t_.asFinite().unwrap();
//         // return getSingletonIterator(t_);
//         return ifElseIter(t.period().isNone()
//             , [=]() { return getSingletonIterator(t_); }
//             , [=]() { 
//               auto p = t.period().unwrap();
//               auto eps = t.epsilon();
//               auto bigPeriod = iterLiraLits(phi)
//                 .map([=](auto l) { return l.term().summary(var); })
//                 // .filter([](auto& l) { return l.off != 0; })
//                 .map([=](auto l) { return l.per; })
//                 .fold([=](auto l, auto r) { return qLcm(l,r); })
//                 .unwrap();
//
//               auto aperiodicLits = [=]() { 
//                 return iterLiraLits(phi)
//                   .map([=](auto l) { return l.term().summary(var); })
//                   .filter([](auto& phi) { return phi.off != 0; }); 
//               };
//               auto intervals = ifElseIter(aperiodicLits().hasNext(),
//                   [=]() { return aperiodicLits()
//                                    .map([=](auto phi) { return make_pair(phi.lowerX(), bigPeriod + phi.deltaX()); }); },
//                   [=]() { return getSingletonIterator(make_pair(R::zero(), bigPeriod)); });
//
//               return intervals
//                 .flatMap([=](auto inter) { 
//                     // auto phi = l.term().summary(var);
//                     return Grid(t)
//                       .intersect(true, inter.first, inter.second, true); })
//                       .map([=](auto t2) { return ElimTerm(FiniteElimTerm(t2, eps, {})); })
//                           ;
//               }
//             );
//     });
// }



#define BIN_OP(op, Class)                                                                 \
  LiraFormula operator op(std::shared_ptr<LiraFormula> const& lhs, std::shared_ptr<LiraFormula> const& rhs) \
  { return LiraFormula(Class { lhs, rhs, }); }                                              \
                                                                                          \
  LiraFormula operator op(LiraFormula const& lhs, std::shared_ptr<LiraFormula> const& rhs)      \
  { return make_shared(lhs)  op rhs; }                                                    \
                                                                                          \
  LiraFormula operator op(std::shared_ptr<LiraFormula> const& lhs, LiraFormula const& rhs)      \
  { return lhs  op make_shared(rhs); }                                                    \
                                                                                          \
  LiraFormula operator op(LiraFormula const& lhs, LiraFormula const& rhs)                       \
  { return lhs  op make_shared(rhs); }                                                    \

BIN_OP(&&, Conj)
BIN_OP(||, Disj)

Option<Numeral> trivEval(LiraTerm const& phi)
{
  auto simpl = PolynomialEvaluation::evaluate(phi.toNormalTerm());
  return R::tryNumeral(simpl);
  // return phi.match(
  //       [&](TermList var) -> Option<Numeral> { return {}; }
  //     , [&]() { return some(Numeral(1)); }
  //     , [&](Numeral k, LiraTerm t) { 
  //         return k == 0 ? some(Numeral(0)) 
  //                       : trivEval(t).map([&](auto n) { return k * n; }); 
  //       }
  //     , [&](LiraTerm lhs, LiraTerm rhs) { 
  //         auto l = trivEval(lhs);
  //         if (l.isNone()) return l;
  //         auto r = trivEval(rhs);
  //         if (r.isNone()) return r;
  //         return some(*l + *r);
  //       }      
  //     , [&](LiraTerm t) { 
  //         return trivEval(t).map([](auto n) { return n.floor(); });
  //     });
}

// Option<Numeral> trivEval(LiraTerm const& phi)
// {
//   return phi.match(
//         [&](TermList var) -> Option<Numeral> { return {}; }
//       , [&]() { return some(Numeral(1)); }
//       , [&](Numeral k, LiraTerm t) { 
//           return k == 0 ? some(Numeral(0)) 
//                         : trivEval(t).map([&](auto n) { return k * n; }); 
//         }
//       , [&](LiraTerm lhs, LiraTerm rhs) { 
//           auto l = trivEval(lhs);
//           if (l.isNone()) return l;
//           auto r = trivEval(rhs);
//           if (r.isNone()) return r;
//           return some(*l + *r);
//         }      
//       , [&](LiraTerm t) { 
//           return trivEval(t).map([](auto n) { return n.floor(); });
//       });
// }

Option<bool> trivEval(LiraLit const& phi) {
  return trivEval(phi.term())
    .map([&](Numeral const& n) {
        switch (phi.connective()) {
          case LiraPred::Greater: return n >  0;
          case LiraPred::Geq:     return n >= 0;
          case LiraPred::Neq:     return n != 0;
          case LiraPred::Eq:      return n == 0;
        }});
}

LiraFormula vsubs(LiraLit const& phi, TermList var, FiniteElimTerm const& val) 
{
  ASS(val.period().isNone())

  if (val.epsilon().isNone())  {
    return LiraFormula(LiraLiteral(LiraLit(EqHelper::replace(phi.term().toNormalTerm(), var, val.term()), phi.connective())));
  } else {
    auto sum = phi.term().summary(var);
    auto limSubs = [&]() { return EqHelper::replace(sum.lim, var, val.term()); };
    if (isIneq(phi.connective()))  {
      return LiraFormula(LiraLiteral(LiraLit(limSubs()
                          , sum.slope >  0 ? LiraPred::Geq 
                          : sum.slope == 0 ? phi.connective()
                          :                  LiraPred::Greater)));
    } else {
      return LiraFormula(LiraLiteral(LiraLit(sum.slope == 0 ? limSubs()         // <- (~) lim[t] = 0
                                              : R::constantTl(1), // <- (~) 1 = 0
                                              phi.connective())));
    }

  }
}


LiraFormula vsubs(EpsLit const& lit, TermList var, FiniteElimTerm const& val)
{ 
  auto phi = lit.term();
  ASS(val.period().isNone())
  if (val.epsilon()) {
    auto sum = phi.summary(var);
    auto limT = EqHelper::replace(sum.lim, var, val.term());
    return LiraFormula(
        sum.slope == 1 ? LiraLiteral(LiraLit(limT, LiraPred::Neq))
                       : LiraLiteral(EpsLit((1 / (1 - sum.slope)) * limT)));
  } else {
    /* phi[x//t] !~ eps => phi[x/t] !~ eps */ 
    return LiraFormula(LiraLiteral(EpsLit(EqHelper::replace(phi.toNormalTerm(), var, val.term()))));
  }
}

Stack<LiraLit> vsubs(Stack<LiraLit> const& phi, TermList var, ElimTerm const& val) 
{ 
  return arrayIter(phi)
           .map([&](auto phi) { return vsubs(phi, var, val.asFinite().unwrap()).template unwrap<LiraLiteral>().template unwrap<LiraLit>(); })
           .template collect<Stack>(); 
}



LiraFormula vsubs(LiraLiteral const& phi, TermList var, FiniteElimTerm const& val) 
{ return phi.apply([&](auto l) { return vsubs(l, var, val); }); }

LiraFormula vsubs(LiraFormula const& phi, TermList var, FiniteElimTerm const& val)
{
  ASS(val.period().isNone())

  return phi.match(
      [&](LiraLiteral const& l) { return vsubs(l, var, val); },
      [&](Conj const& c) { return vsubs(*c.lhs, var, val) && vsubs(*c.rhs,var,val); },
      [&](Disj const& c) { return vsubs(*c.lhs, var, val) || vsubs(*c.rhs,var,val); });
}


LiraFormula vsubs(LiraFormula const& phi, TermList var, ElimTerm val)
{ return vsubs(phi, var, *val.asFinite()); }

LiraFormula vsubs(LiraFormula const& phi, Assignments const& asgn) {
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

struct True {
  friend std::ostream& operator<<(std::ostream& out, True const& self)
  { return out << "true"; }
};
struct False { 
  LiraLiteral lit; 
  friend std::ostream& operator<<(std::ostream& out, False const& self)
  { return out << "false ( " << self.lit << " )"; }
};
struct Unknown {
  friend std::ostream& operator<<(std::ostream& out, Unknown const& self)
  { return out << "unknown"; }
};
using TrivEvalResult = Coproduct<True, False, Unknown>;

TrivEvalResult trivEval(LiraFormula const& phi) {
  return phi.match(
      [&](LiraLiteral const& l) { 
        auto r = trivEval(l); 
        return r.isNone() ? TrivEvalResult(Unknown{})
             : *r         ? TrivEvalResult(True{})
             :              TrivEvalResult(False{l});
      },
      [&](Conj const& c) {
        auto l = trivEval(*c.lhs);
        auto r = trivEval(*c.lhs);
        if (!l.template is<Unknown>()) {
          return l.is<False>() ? l : r;
        } else if (!r.template is<Unknown>()) {
          return r.is<False>() ? r : l;
        } else {
          return l;
        }
      },
      [&](Disj const& c) -> TrivEvalResult {
        ASSERTION_VIOLATION_REP("TODO")
        // auto l = trivEval(*c.lhs);
        // auto r = trivEval(*c.lhs);
        // if (l.isSome()) {
        //   return true == *l ? some(true) : r;
        // } else if (r.isSome()) {
        //   return true == *r ? some(true) : l;
        // } else {
        //   ASS(l.isNone() && r.isNone())
        //   return {};
        // }
      });
}

// Option<bool> trivEval(LiraFormula const& phi) {
//   return phi.match(
//       [&](LiraLiteral const& l) { return trivEval(l); },
//       [&](Conj const& c) -> Option<bool> {
//         auto l = trivEval(*c.lhs);
//         auto r = trivEval(*c.lhs);
//         if (l.isSome()) {
//           return false == *l ? some(false) : r;
//         } else if (r.isSome()) {
//           return false == *r ? some(false) : l;
//         } else {
//           ASS(l.isNone() && r.isNone())
//           return {};
//         }
//       },
//       [&](Disj const& c) -> Option<bool> {
//         auto l = trivEval(*c.lhs);
//         auto r = trivEval(*c.lhs);
//         if (l.isSome()) {
//           return true == *l ? some(true) : r;
//         } else if (r.isSome()) {
//           return true == *r ? some(true) : l;
//         } else {
//           ASS(l.isNone() && r.isNone())
//           return {};
//         }
//       });
// }

template<class F>
auto tupMatch1(F f) 
{ return [f = std::move(f)](auto tup) { return f(std::get<0>(tup)); }; }


template<class F>
auto tupMatch2(F f) 
{ return [f = std::move(f)](auto tup) { return f(std::get<0>(tup), std::get<1>(tup)); }; }


template<class F>
auto tupMatch3(F f) 
{ return [f = std::move(f)](auto tup) { return f(std::get<0>(tup), std::get<1>(tup), std::get<2>(tup)); }; }

bool _decide(Stack<TermList> vars, Stack<LiraLit> const& lits) 
{
#define DEBUG_DECIDE(lvl, ...) if (lvl < 2) DBG(outputInterleaved("", range(0, state.size()).map([](auto) { return "|  "; })), __VA_ARGS__)

  Assignments assignment;
  struct DecisionLevel {
    Stack<LiraLit> phi;
    Stack<LiraLit> lemmas;
  };
  Stack<std::unique_ptr<DecisionLevel>> state;
  // Stack<Stack<LiraLit>> phi_history;
  // Stack<Stack<LiraLit>> lemma_history;
  auto phi = [&]() -> Stack<LiraLit>& { return state.top()->phi; };
  auto lemmas = [&]() -> Stack<LiraLit>& { return state.top()->lemmas; };
  // Stack<std::shared_ptr<LiraFormula>> phi_hist;
  if (lits.isEmpty()) return true;
  // phi_history.push(lits);
  // phi_hist.push(make_shared(arrayIter(lits)
  //     .map([](auto l) { return LiraLiteral(l); })
  //     .map([](auto l) { return LiraFormula(l); })
  //     .fold([](auto l, auto r) { return l && r; })
  //     .unwrap()));
  // Stack<std::shared_ptr<LiraFormula>> lemma_hist;
  // lemma_hist.push(make_shared(LiraFormula::top()));
  state.push(make_unique(DecisionLevel {
      .phi = lits,
      .lemmas = Stack<LiraLit>(),
  }));
  DEBUG_DECIDE(0, "input: ", lits)
  auto learn = [&]() -> LiraFormula {
    ASSERTION_VIOLATION_REP("TODO")};

  do {
    // auto triv = trivEval(phi_hist.top() && lemma_hist.top());
    // if (triv.isSome()) {
    //   if (*triv) {
    //     return true;
    //   } else {
    //     auto lemma = make_shared(learn());
    //     while (triv.isSome()) {
    //       lemma_hist.pop();
    //       phi_hist.pop();
    //       vars.push(assignment.pop().var);
    //       triv = trivEval(phi_hist.top() && lemma_hist.top());
    //       ASS_REP(triv != some(true), "assigning less variables cannot make the formula true")
    //     }
    //     for (auto& p : lemma_hist) {
    //       p = make_shared(p && lemma);
    //     }
    //   }
    // }
    ASS_REP(vars.isNonEmpty(), outputToString("unexpeced unbound variables in ", lits))
    auto var = vars.pop();
    Recycled<Stack<std::tuple<ElimTerm, unsigned, bool>>> failed;
    Option<ElimTerm> val;
    // for (auto t : simplIter(elimSet(var, phi()))) {
    for (auto t : simplIter(flattenPeriods(var, phi(), simplIter(elimSet(var, phi()))))) {
      // DEBUG_DECIDE(0, "------------------------------------------ ")
      auto phiS = vsubs(phi(), var, t);
      auto lemS = vsubs(lemmas(), var, t);

      // auto phiS = make_shared(vsubs(*phi_hist.top(), var, t));
      // auto lemmaS = make_shared(vsubs(*lemma_hist.top(), var, t));
      DEBUG_DECIDE(0, "trying assigment ", var, " -> ", t)
      // auto triv = trivEval(phiS && lemmaS);
      auto lits = 
        concatIters(
          range(0, phi().size())
            .map([](auto i) { return make_tuple(i, false); }),
          range(0, lemmas().size())
            .map([](auto i) { return make_tuple(i, true); }));
        // .inspect(tupMatch3([](LiraLit lit, unsigned, unsigned) { return trivEval(lit) == some(false); }))
        // .map(tupMatch3([](LiraLit lit, unsigned, unsigned) { return make_tuple(trivEval(lit) )== some(false); }))
        // .find(tupMatch3([](LiraLit lit, unsigned, unsigned) { return trivEval(lit) == some(false); }))
        ;

      bool anyUnknown = false;
      bool anyFailed = false;
      for (auto id : lits) {
        auto idx = std::get<0>(id); 
        auto isLem = std::get<1>(id); 
        auto lit = (isLem ? lemS[idx] : phiS[idx]);
        auto triv = trivEval(lit);
        DEBUG_DECIDE(2, lit, " -> ", triv)
        if (triv == some(false)) {
          failed->push(std::make_tuple(t, idx, isLem));
          anyFailed = true;
          DEBUG_DECIDE(1, "false: ", lit)
          break;
        } else if (triv.isNone()) {
          anyUnknown = true;
        }
      }

      // DBG("triv eval result: ", triv)
      if (!anyFailed) {
        state.push(make_unique(DecisionLevel {
            .phi = phiS,
            .lemmas = lemS,
        }));
        DEBUG_DECIDE(0, "new literals: ", phiS)
        DEBUG_DECIDE(0, "new lemmas: "  , lemS)
        val = some(t);
        if (anyUnknown) {
          break;
        } else {
          return true;
        }
        // phi_hist.push(phiS);
        // lemma_hist.push(lemmaS);
      } else {
        DEBUG_DECIDE(0, "------------------------------------------")
      }
    }
    DEBUG_DECIDE(0, "------------------------------------------")

    if (val.isNone()) {
      DEBUG_DECIDE(0, "conflicting assignment: ", assignment)
      // DEBUG_DECIDE(0, "conflict for ", var)
      // DEBUG_DECIDE(2, assignment)
      // for (auto i : range(0, assignment.size())) {
      //   auto a = assignment[i];
      //   auto newVar = (i < assignment.size()) ? assignment[i + 1].var : var;
      //   DBGE(a, " ==> ", elimSet())
      // }
      // for (auto&& a : assignment.iter()) {
      //   DBG(a, "\t", elimSet())
      // }
      for (auto fail : *failed) {
        auto elimTerm = std::get<0>(fail); 
        auto idx = std::get<1>(fail); 
        auto isLem = std::get<2>(fail); 
        auto lit = [&](auto& state) { return (isLem ? state->lemmas[idx] : state->phi[idx]); };
        // auto lit = (isLem ? state[0].lemmas[idx] : state[0].phi[idx]);
        DEBUG_DECIDE(2, var, " // ", elimTerm, "\t conflict literal ", dbgIter(simplIter(arrayIter(state).map(lit))));
      }
      ASSERTION_VIOLATION

      // auto lemma = learn();
      // state[0].lemmas.extend(lemma);
      // for (auto i : range(0, assignment.size())) {
      //
      // }

      // DBGE(dbgIter(simplIter(failed->iter())))
      // var cannot be assigned to any value, we need to learn a lemma why that 
      // prevents the current assignment of the other variables
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
  auto ls = arrayIter(lits).map([](auto l) { return LiraLit::from(l); }).template collect<Stack>();
  return _decide(vars, ls);
}

} // namespace CDVS

} // namespace QE


