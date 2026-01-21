/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "QKbo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Lib/Option.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Theory.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG_QKBO(lvl, ...) if (lvl < 0) {DBG(__VA_ARGS__)}

namespace Kernel {

  // TODO use outputToString
template<class T>
std::string output_to_string(T const& t) 
{
  std::stringstream out;
  out << t;
  return out.str();
}

using OU = OrderingUtils;

QKbo::QKbo(KBO kbo, std::shared_ptr<InequalityNormalizer> norm) 
  : _norm(std::move(norm))
  , _kbo(std::move(kbo))
{
  ASS(_kbo.usesQkboPrecedence())
}

using MulExtMemo = DArray<Option<Ordering::Result>>;

RationalConstantType rat(int n) { return RationalConstantType(IntegerConstantType(n), IntegerConstantType(1)); };
RationalConstantType rat(IntegerConstantType n) { return RationalConstantType(n, IntegerConstantType(1)); };
template<class T> RationalConstantType rat(T n) { return RationalConstantType(n);    };

QKbo::Result QKbo::compare(Literal* l1, Literal* l2) const 
{
  if (l1 == l2) 
    return Result::EQUAL;

  auto i1 = AlascaState::interpretedPred(l1);
  auto i2 = AlascaState::interpretedPred(l2);
       if ( i1 && !i2) return Result::LESS;
  else if (!i1 &&  i2) return Result::GREATER;
  else if (!i1 && !i2) return TIME_TRACE_EXPR("uninterpreted", OU::lexProductCapture(
        [&]() { return _kbo.comparePredicatePrecedences(l1->functor(), l2->functor()); }
      , [&]() { return OU::lexExt(termArgIter(l1), termArgIter(l2), this->asClosure()); }
      , [&]() { return OU::stdCompare(l1->isNegative(), l2->isNegative()); }
    ));
  else {
    ASS(i1 && i2)
   
    auto a1_ = atomsWithLvl(l1);
    auto a2_ = atomsWithLvl(l2);
    if (!a1_.isSome() || !a2_.isSome())
      return Result::INCOMPARABLE;
    auto& a1 = a1_.unwrap();
    auto& a2 = a2_.unwrap();
    return OU::lexProductCapture(
        [&]() -> Ordering::Result { 
        TIME_TRACE("atoms with levels")
        return OU::weightedMulExt(*std::get<0>(a1), *std::get<0>(a2), 
                          [&](auto const& l, auto const& r)
                          { return OU::lexProductCapture(
                              [&]() { return this->compare(l.term, r.term); }
                            , [&]() { return OU::stdCompare(std::get<1>(a1),std::get<1>(a2)); }
                          );}); }
      , [&]() {
        // the atoms of the two literals are the same. 
        // This means they must be of the same sort
        auto sort =  SortHelper::getTermArgSort(l1,0);
        ASS_EQ(sort, SortHelper::getTermArgSort(l2,0));
        ASS_EQ(l1->isEquality() && l1->isPositive(), l2->isEquality() && l2->isPositive())
        return tryNumTraits([&](auto numTraits) {
          using NumTraits = decltype(numTraits);
          if (NumTraits::sort() != sort) {
            return Option<Ordering::Result>();
          } else {
            if (l1->isEquality() && l2->isEquality()) {
              TIME_TRACE("compare equalities")
              ASS_EQ(l1->isPositive(), l2->isPositive())
              return Option<Ordering::Result>(OU::lexProductCapture(
                  // TODO make use of the constant size of the multiset
                  [&]() { 
                    auto e1 = nfEquality<NumTraits>(l1);
                    auto e2 = nfEquality<NumTraits>(l2);
                    return OU::mulExt(*e1, *e2, this->asClosure()); }
                , [&]() { 
                  Recycled<MultiSet<TermList>> m1; m1->init(l1->termArg(0), l1->termArg(1));
                  Recycled<MultiSet<TermList>> m2; m2->init(l2->termArg(0), l2->termArg(1));
                  // TODO make use of the constant size of the multiset
                  return OU::mulExt(*m1,*m2,this->asClosure()); }
              ));
            } else if ( l1->isEquality() && !l2->isEquality()) {
              ASS(l1->isNegative())
              return Option<Ordering::Result>(Result::LESS);
            } else if (!l1->isEquality() &&  l2->isEquality()) {
              ASS(l2->isNegative())
              return Option<Ordering::Result>(Result::GREATER);
            } else if (l1->functor() == NumTraits::isIntF()) {
              ASS_EQ(l2->functor(), NumTraits::isIntF())
              ASS_EQ(l2->isPositive(), l1->isPositive())
              return some(this->compare(l1->termArg(0), l2->termArg(0)));
            } else {
              TIME_TRACE("compare inequqlities")
              ASS(l1->functor() == numTraits.greaterF() || l1->functor() == numTraits.geqF())
              ASS(l2->functor() == numTraits.greaterF() || l2->functor() == numTraits.geqF())
              ASS(l1->isPositive())
              ASS(l2->isPositive())
              return Option<Ordering::Result>(OU::lexProductCapture(
                  [&]() { return this->compare(l1->termArg(0), l2->termArg(0)); }
                , [&]() { return _kbo.comparePredicatePrecedences(l1->functor(), l2->functor()); }
              ));
            } 
          } 
        }) || [&]() {
          ASS_EQ(l1->isPositive(), l2->isPositive())
          // uninterpreted sort
          return Result::EQUAL;
        };
      }
    );
  }
}

bool interpretedFun(Term* t) {
  auto f = t->functor();
  return forAnyNumTraits([&](auto numTraits) -> bool {
      return f == numTraits.addF()
         || (f == numTraits.mulF() && numTraits.isNumeral(*t->nthArgument(0)))
         || numTraits.isNumeral(t);
  });
}

bool uninterpretedFun(Term* t) 
{ return !interpretedFun(t); }


auto toNumeralMul(TermList t) -> std::tuple<Option<TermList>, RationalConstantType> {
  if (t.isVar()) {
    return std::make_tuple(Option<TermList>(t), rat(1));
  } else {
    auto term = t.term();
    auto f = term->functor();
    auto sort = SortHelper::getResultSort(term);
    return tryNumTraits([&](auto numTraits) {
        if (sort != numTraits.sort()) {
          return Option<std::tuple<Option<TermList>, RationalConstantType>>();

        } else if (f == numTraits.mulF() && numTraits.isNumeral(*term->nthArgument(0))) {
          /* t = k * t' ( for some numeral k ) */
          return some(std::make_tuple(
                some(*term->nthArgument(1)),  /* <- t' */
                rat(numTraits.tryNumeral(*term->nthArgument(0)).unwrap()) /* <- k */
                ));

        } else if (numTraits.isNumeral(t)) {
          /* t is a numeral */
          return some(std::make_tuple(
                Option<TermList>(), 
                rat(numTraits.tryNumeral(t).unwrap())
                ));

        } else {
          /* t is uninterpreted */
          return some(std::make_tuple(Option<TermList>(t), RationalConstantType(1)));
        }
    }).unwrap();
  }
}


Ordering::Result QKbo::compare(TermList s, TermList t) const 
{
  if (s.isVar() && t.isVar()) 
    return s == t ? Ordering::EQUAL : Ordering::INCOMPARABLE;

  if (s.isTerm() && t.isTerm() && norm().equivalent(s.term(), t.term()))
    return Ordering::EQUAL;

  auto as = abstr(s);
  auto at = abstr(t);
  DEBUG_QKBO(0, "abstr(s): ", as)
  DEBUG_QKBO(0, "abstr(t): ", at)
  // TODO subterm modulo Tsigma
  if (as.isNone() || at.isNone()) {
    return Ordering::Result::INCOMPARABLE;

  } else {
    auto cmp = _kbo.compare(as.unwrap(), at.unwrap());
    switch (cmp) {
      case Ordering::GREATER:      return Ordering::GREATER;
      case Ordering::LESS:         return Ordering::LESS;
      case Ordering::INCOMPARABLE: return Ordering::INCOMPARABLE;
      case Ordering::EQUAL: 
        ASS_EQ(as.unwrap(), at.unwrap())
        return cmpNonAbstr(s,t);
      default:;
    }
    ASSERTION_VIOLATION
  }
}


/// case 2. precondition: we know that abstr(t1) == abstr(t2)
Ordering::Result QKbo::cmpNonAbstr(TermList t1, TermList t2) const 
{
  if (t1 == t2) return Result::EQUAL;
  if (t1.isTerm() && t2.isTerm() 
      && t1.term()->functor() == t2.term()->functor() 
      && uninterpretedFun(t1.term())) {
    // 2.a) LEX
    return OrderingUtils::lexExt(termArgIter(t1.term()), termArgIter(t2.term()), 
          [&](auto l, auto r) { return this->compare(l,r); });

  } else {
    // 2.b) interpreted stuff
    if (t1.isVar() && t2.isVar()) {
      ASS_NEQ(t1, t2);
      return INCOMPARABLE;
    }

    return forAnyNumTraits([&](auto numTraits){
        using NumTraits = decltype(numTraits);
        if (
               ( t1.isTerm() && SortHelper::getResultSort(t1.term()) == numTraits.sort() )
            || ( t2.isTerm() && SortHelper::getResultSort(t2.term()) == numTraits.sort() )
            ) {
          auto a1 = signedAtoms<NumTraits>(t1);
          auto a2 = signedAtoms<NumTraits>(t2);
          if (a1.isNone() || a2.isNone()) {
            return Option<Result>(Result::INCOMPARABLE);
          } else {
            return Option<Result>(OU::weightedMulExt(*a1.unwrap(), *a2.unwrap(),
                  [this](auto& l, auto& r) 
                  { return OU::lexProductCapture(
                      [&]() { return this->compare(l.term, r.term); },
                      [&]() { return OU::stdCompare(l.sign, r.sign); }); }));
          }
        } else {
          return Option<Result>();
        }
    }) || []() -> Result { ASSERTION_VIOLATION };
  }
}


Option<TermList> QKbo::abstr(TermList t) const 
{
  t = this->norm().normalize(t).denormalize();
  using Out = Option<TermList>;
  if (t.isVar()) {
    return Option<TermList>(t);
  } else {
    auto term = t.term();
    auto f = term->functor();
    auto res = tryNumTraits([&](auto n) -> Option<Option<TermList>> {
        using NumTraits = decltype(n);
        auto noAbstraction = []() { return Option<Option<TermList>>(Option<TermList>()); };
        if (asig(n).isNumeral(t)) {
          return some(some(asig(n).one()));

        } else if (   
          /* t = t1 + ... + tn */
               asig(n).isAdd(f)
          /* t = k * t' */
          || ( asig(n).isLinMul(f) )
          ) {
          auto norm = this->norm().normalize(TypedTermList(term)).wrapPoly<NumTraits>();
          RStack<TermList> abstracted_;
          auto& abstracted = *abstracted_;
          abstracted.reserve(norm->nSummands());
          for (auto monom : norm->iterSummands()) {
            auto a = abstr(monom.factors->denormalize());
            if (a.isNone()) {
              return noAbstraction();
            } else {
              abstracted.push(*a);
            }
          }
          ASS(abstracted.size() > 0)
            // TODO optimize
          for (auto i : range(0, abstracted.size())) {
            for (auto j : range(0, abstracted.size())) {
              auto cmp = _kbo.compare(abstracted[i], abstracted[j]);
              switch(cmp) {
                case Ordering::GREATER:
                case Ordering::EQUAL:
                  /* ok */
                  break; 
                case Ordering::LESS:
                case Ordering::INCOMPARABLE:
                  goto try_next_max;
                  break;
              }
            }
            return Option<Option<TermList>>(Option<TermList>(abstracted[i]));
try_next_max: {}
          }
          return noAbstraction();
        } else {
          // wrong number type or uninterpreted function
          return Option<Option<TermList>>();
        }
    });
    if (res.isSome()) {
      return res.unwrap();
    } else {
      Recycled<Stack<TermList>> args;
      args->loadFromIterator(typeArgIter(term));
      for (auto a : termArgIter(term)) {
        auto abs = abstr(a);
        if (abs.isNone()) {
          return abs;
        } else {
          args->push(abs.unwrap());
        }
      }
      return Out(TermList(Term::create(term, args->begin())));
    }
  }
}

bool Kernel::QKbo::hasSubstitutionProperty(SignedAtoms const& l) const
{

  auto maybeEquiv = [this](TermList l, TermList r) -> bool 
  {
    ASS_NEQ(l, r)

    if (l.ground() && r.ground()) {
      return norm().equivalent(l.term(), r.term());
 

      // TODO tidier(?)
    } else if (AbstractingUnifier::unify(l, 0, r, 0, env.options->unificationWithAbstraction(), env.options->unificationWithAbstractionFixedPointIteration()).isSome()) {
      return true;

    } else {
      return false;
    }
  };

  Stack<TermList> pos;
  Stack<TermList> neg;
  for (auto const& t_ : l.elems.iter()) {
    auto const& sign = std::get<0>(t_).sign;
    auto const& term = std::get<0>(t_).term;

    if (term.isVar() && sign != Sign::Zero) {
      if (concatIters(pos.iterFifo(), neg.iterFifo()).any([&](auto s) { return maybeEquiv(s, term); })) {
        return false;
      }
      pos.push(term);
      neg.push(term);
    } else if (sign != Sign::Zero) {

      auto& same  = sign == Sign::Pos ? pos : neg;
      auto& other = sign == Sign::Pos ? neg : pos;

      if (iterTraits(other.iterFifo())
        .any([&](auto s) { return maybeEquiv(s, term); })) 
      {
          return false;
      }
      same.push(term);
    }
  }
  return true;
}



void QKbo::show(std::ostream& out) const 
{ _kbo.show(out); }

} // Kernel
