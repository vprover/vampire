#include "LaKbo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {

LaKbo::LaKbo(KBO kbo) 
  : KBO(std::move(kbo))
  , _shared(make_shared(new Kernel::IrcState {
        .normalizer = InequalityNormalizer(), 
        .ordering = this,
        .uwa = env.options->unificationWithAbstraction(),
  }))
{
}

template<class Trm, class Cmp>
auto multisetCmpSorted(Stack<Trm> s1, Stack<Trm> s2, Cmp cmp) -> LaKbo::Result
{
  /* remove equal elements. we assume that s1 and s2 are sorted. */
  unsigned i1 = 0;
  unsigned o1 = 0;
  unsigned i2 = 0;
  unsigned o2 = 0;
  auto keep = [](Stack<Trm>& stack, unsigned& index, unsigned& offset) 
  { stack[offset++] = stack[index++]; };
  auto rm = [&]() { i1++; i2++; };
  auto keep1 = [&]() { keep(s1, i1, o1); };
  auto keep2 = [&]() { keep(s2, i2, o2); };
  while (i1 < s1.size() && i2 < s2.size()) {
    if (s1[i1] == s2[i2]) {
      rm();
    } else if (s1[i1] < s2[i2]) {
      keep1();
    } else {
      keep2();
    }
  }
  while(i1 < s1.size()) 
    keep1();
  while(i2 < s2.size())
    keep2();

  s1.truncate(o1);
  s2.truncate(o2);

  if (s1.isEmpty() && s2.isEmpty()) {
    return LaKbo::Result::EQUAL;
  } else if (s1.isEmpty()) {
    return LaKbo::LESS;
  } else if (s2.isEmpty()) {
    return LaKbo::GREATER;
  }

  auto checkAllDominated = [&](Stack<Trm> const& s1, Stack<Trm> const& s2) {
    for (auto e1 : s1) {
      if (!iterTraits(s2.iterFifo())
          .find([&](Trm e2) { return cmp(e1, e2) == LaKbo::LESS; })
          .isSome()) {
        return false;
      }
    }
    return true;
  };
  auto dom1 = checkAllDominated(s1, s2);
  auto dom2 = checkAllDominated(s2, s1);
  ASS(!dom1 || !dom2);
  if (dom1)  {
    return LaKbo::LESS;
  } else if (dom2) {
    return LaKbo::GREATER;
  } else {
    return LaKbo::INCOMPARABLE;
  }
}

template<class Trm, class Cmp>
auto multisetCmp(Stack<Trm> s1, Stack<Trm> s2, Cmp cmp) -> LaKbo::Result
{
  std::sort(s1.begin(), s1.end());
  std::sort(s2.begin(), s2.end());
  return multisetCmpSorted(std::move(s1), std::move(s2), cmp);
}


Literal* normalizeLiteral(Literal* lit) 
{
  Stack<TermList> args(lit->arity());
  for (unsigned i = 0; i < lit->arity(); i++) {
    args.push(normalizeTerm(*lit->nthArgument(i), SortHelper::getArgSort(lit, i)).denormalize());
  }
  return Literal::create(lit, args.begin());
}

template<class F, class... As>
auto zipVariants(Coproduct<As...>& lhs, Coproduct<As...>& rhs, F f)
{
  return lhs.apply([&](auto&& lhs) {
      using T = rm_ref_t<decltype(lhs)>;
      return rhs.template as<T>()
                .map([&](auto&& rhs) 
                    { return f(lhs,rhs); });
  });
}

LaKbo::Result LaKbo::compare(Literal* l1_, Literal* l2_) const 
{
  CALL("LaKbo::compare(Literal*, Literal*)");
  auto inner = [&]() {

    auto l1 = normalizeLiteral(l1_);
    auto l2 = normalizeLiteral(l2_);

    auto lvlCmp = fromComparison(Int::compare(predicateLevel(l1->functor()), predicateLevel(l2->functor())));
    if (lvlCmp != Result::EQUAL) {
      return _reverseLCM ? Ordering::reverse(lvlCmp) : lvlCmp;
    }

    if (l1 == l2) return Result::EQUAL;
    if (l1 == Literal::complementaryLiteral(l2)) return l1->isNegative() ? Result::LESS : Result::GREATER;

    auto irc1 = _shared->normalize(l1);
    auto irc2 = _shared->normalize(l2);
    auto ircResult = irc1.isNone() || irc2.isNone() 
      ? Option<Result>() 
      : zipVariants(irc1.unwrap(), irc2.unwrap(), [&](auto&& irc1, auto&& irc2) {
            using Numeral = typename std::remove_reference_t<decltype(irc1)>::NumTraits::ConstantType;

            auto result = Result::EQUAL;

            // compare atomic term multisets
            // if (result == Result::EQUAL) {
            //   result = multisetCmp(
            //     irc1.term().iterSummands().map([](auto x) { return x.factors; }).template collect<Stack>(),
            //     irc2.term().iterSummands().map([](auto x) { return x.factors; }).template collect<Stack>(),
            //     [&](auto lhs, auto rhs) { 
            //         return (lhs == rhs) ? Result::EQUAL : this->compare(lhs->denormalize(), rhs->denormalize());
            //     });
            // }

            // compare atomic term + numeral multisets
            if (result == Result::EQUAL) {
              result = multisetCmp(
                irc1.term().iterSummands().template collect<Stack>(),
                irc2.term().iterSummands().template collect<Stack>(),
                [&](auto lhs, auto rhs) { 
                  CALL("LaKbo::comparePredicates@closure1")
                  if (lhs.factors == rhs.factors) {
                    switch (Numeral::comparePrecedence(lhs.numeral, rhs.numeral)) {
                      case Comparison::LESS: return Result::LESS;
                      case Comparison::GREATER: return Result::GREATER;
                      case Comparison::EQUAL: return Result::EQUAL;
                    }
                  } else {
                    return this->compare(lhs.factors->denormalize(), rhs.factors->denormalize());
                  }
                });
            }

            // compare symbol
            if (result == Result::EQUAL) {
              result = Kernel::compare(irc1.symbol(), irc2.symbol());
            }

            if(result == Result::EQUAL && irc1.term() != irc2.term())  {
              return Result::INCOMPARABLE;
            } else {
              return result;
            }
          });

    if (ircResult.isSome()) {
      return ircResult.unwrap();
    } else {
      auto e1 = l1->isEquality();
      auto e2 = l2->isEquality();
      if (e1 && e2) {
        return KBO::compareEqualities(l1, l2);
      } else if (e1 && !e2) {
        return Result::LESS;
      } else if (!e1 && e2) {
        return Result::GREATER;
      } else {
        ASS(!e1 && !e2);
        return KBO::comparePredicates(l1, l2);
      }
    }
  };
  DEBUG("lhs: ", *l1_)
  DEBUG("rhs: ", *l2_)
  auto out = inner();
  DEBUG("out: ", out)
  return out;
}

Ordering::Result LaKbo::compare(TermList t1_, TermList t2_) const 
{
  CALL("LaKbo::compare")
  return KBO::compare(t1_,t2_);
  // auto inner = [&]() {
  //   if (t1_ == t2_) return Result::EQUAL;
  //   auto norm = [](TermList t) { return t.isVar() ? t : normalizeTerm(t.term()).denormalize(); };
  //   auto res = TraversalResult::initial(); 
  //   auto t1 = norm(t1_), t2 = norm(t2_);
  //   traverse(res, t1, t2);
  //   auto out = toOrdering(res);
  //   return out == EQUAL ? INCOMPARABLE  // <- only equal modulo AC+numeral
  //                       : out;
  // };
  // DEBUG("lhs: ", t1_)
  // DEBUG("rhs: ", t2_)
  // auto out = inner();
  // DEBUG("out: ", out)
  // return out;
}

void LaKbo::show(ostream& out) const 
{ KBO::show(out); }

Comparison LaKbo::compareFunctors(unsigned fun1, unsigned fun2) const 
{ return KBO::compareFunctors(fun1,fun2); }


// struct NumeralMultiplication {
//   TermList numeral;
//   TermList nonNumeral;
// };
//
// template<class NumTraits>
// Option<NumeralMultiplication> tryNumeralMultiplication(Term* t)
// {
//   if (t->functor() == NumTraits::mulF()) {
//     for (unsigned i : {0, 1}) {
//       if (NumTraits::tryNumeral(*t->nthArgument(i)).isSome()) {
//         return Option<NumeralMultiplication>({
//             .numeral = *t->nthArgument(i),
//             .nonNumeral = *t->nthArgument(1 - i),
//         });
//       }
//     }
//   }
//   return Option<NumeralMultiplication>();
// }
//
// template<class NumTraits>
// Option<TermList> _dropNumeralMultiplications(TermList t)
// {
//   auto nonNumeralPart = [](TermList t) -> Option<TermList> 
//     { 
//       if (t.isVar()) {
//         return Option<TermList>();
//       } else {
//         return tryNumeralMultiplication<NumTraits>(t.term())
//                       .map([](NumeralMultiplication mul){return mul.nonNumeral;}); 
//       }
//     };
//   auto out = nonNumeralPart(t);
//   if (out.isSome()) {
//     for (auto nonNum = out; nonNum.isSome(); nonNum = nonNumeralPart(nonNum.unwrap())) {
//       out = nonNum;
//     }
//     return out;
//   } else {
//     return out;
//   }
// }
//
//
// TermList LaKbo::dropNumeralMultiplications(LaKbo::TraversalResult& res,  TermList t) const
// {
//
//   auto dropped = _dropNumeralMultiplications< IntTraits>(t)
//     || [t]() { return _dropNumeralMultiplications< RatTraits>(t); }
//     || [t]() { return _dropNumeralMultiplications<RealTraits>(t); };
//   return dropped || t;
// }
//
// Option<NumeralMultiplication> tryNumeralMultiplication(Term* t)
// {
//   return tryNumeralMultiplication<IntTraits>(t)
//     || [t]() { return tryNumeralMultiplication< RatTraits>(t); }
//     || [t]() { return tryNumeralMultiplication<RealTraits>(t); };
// }
//
//
// template<class F>
// void LaKbo::traverse(TraversalResult& res, TermList t, int factor, F fun) const
// {
//   ASS(factor == -1 || factor == 1)
//   t = dropNumeralMultiplications(res, t);
//   fun(t);
//   if (t.isTerm()) {
//     auto term = t.term();
//     res.weight_balance += factor * symbolWeight(term);
//     traverse(res, term->args(), factor, fun);
//   } else {
//     res.addVarBalance(t.var(), factor);
//     res.weight_balance += factor * KBO::variableWeight();
//   }
// }
//
//
// void LaKbo::traverse(TraversalResult& res, TermList* tt, int factor) const
// { traverse(res,tt,factor,[](TermList) {} ); }
//
// void LaKbo::traverse(TraversalResult& res, TermList t, int factor) const
// { traverse(res,t,factor,[](TermList) {} ); }
//
// template<class F>
// void LaKbo::traverse(TraversalResult& res, TermList* tt, int factor, F fun) const
// {
//   while (!tt->isEmpty()) {
//     traverse(res, *tt, factor, fun);
//     tt = tt->next();
//   }
// }
//
// void LaKbo::traverseSubterm(TraversalResult& res, Term* t, unsigned var, bool varRhs) const
// {
//   traverse(res, TermList::var(var), varRhs ? 1 : -1);
//   res.side_condition = INCOMPARABLE;
//   traverse(res, TermList(t), varRhs ? -1 : 1, [&](TermList t) { 
//       if (t.isVar() && t.var() == var) { 
//         /* subterm found */
//         res.side_condition = varRhs ? GREATER : LESS;
//       } 
//     });
// }
//
//  
// template<class NumTraits>
// bool isACFunction(unsigned f) 
// { return f == NumTraits::addF() || f == NumTraits::mulF(); }
//
// bool isACFunction(unsigned f)
// { return isACFunction<IntTraits>(f) || isACFunction<RatTraits>(f) || isACFunction<RealTraits>(f); }
//
// void LaKbo::traverseAC(TraversalResult& res, Term* t1, Term* t2) const
// {
//   auto f = t1->functor();
//
//   traverse(res, t1->args(), -1);
//   traverse(res, t2->args(),  1);
//
//   ASS_EQ(t1->functor(), t2->functor());
//   ASS(isACFunction(f));
//
//   class Flattened {
//     Stack<TermList> _smallFns;
//     Stack<TermList> _bigFnsAndVars;
//   public:
//     Flattened(Flattened &&) = default;
//     Flattened(Stack<TermList> small, Stack<TermList> big) 
//       : _smallFns(std::move(small))
//       , _bigFnsAndVars(std::move(big)) {}
//
//     Stack<TermList>& bigFnsAndVars() { return _bigFnsAndVars; }
//     Stack<TermList>& smallFns() { return _smallFns; }
//     unsigned size() const { return _bigFnsAndVars.size() + _smallFns.size(); }
//   };
//
//   /* flattens ac terms into a stack of their arguments.
//      assumes that terms are normalized to (t_1 * (t_2 * (... * t_n))).
//      Also it assumes that t_1 < t_2 < t_n wrt std::less<TermList>. */
//   auto flatten = [&](Term* t) -> Flattened {
//     auto isSmallFn = [&](TermList t) -> bool 
//       { return t.isTerm() &&  compareFunctionPrecedences(t.term()->functor(), f) == Result::LESS; };
//
//     auto small = Stack<TermList>{ };
//     auto big   = Stack<TermList>{ };
//
//     auto insert = [&](TermList t) {
//       ASS(!(t.isTerm() && t.term()->functor() == f));
//       (isSmallFn(t) ? small : big).push(t);
//     };
//     auto cur = TermList(t);
//     while (cur.isTerm() && cur.term()->functor() == f) {
//       auto l = *cur.term()->nthArgument(0);
//       cur = *cur.term()->nthArgument(1);
//       insert(l);
//     }
//     insert(cur);
//
//     return Flattened(std::move(small), std::move(big));
//   };
//
//   auto f1 = flatten(t1);
//   auto f2 = flatten(t2);
//   auto cmpBig = multisetCmpSorted(std::move(f1.bigFnsAndVars()), std::move(f2.bigFnsAndVars()), 
//                    [&](auto l, auto r) { return this->compare(l,r); });
//   switch (cmpBig) {
//     case LESS:    
//     case GREATER: 
//     case INCOMPARABLE:
//       res.side_condition = cmpBig;
//       break;
//     case Result::EQUAL:
//       if (f1.size() < f2.size()) {
//         res.side_condition = Result::LESS;
//       } else if (f1.size() > f2.size()) {
//         res.side_condition = Result::GREATER;
//       } else {
//         res.side_condition = multisetCmpSorted(std::move(f1.smallFns()), std::move(f2.smallFns()),
//                                [&](auto l, auto r) { return this->compare(l,r); });
//       }
//       break;
//     default:
//       ASSERTION_VIOLATION
//   }
// }
//
// void LaKbo::traverseLex(TraversalResult& res, TermList* tt1, TermList* tt2) const
// {
//   while (!tt1->isEmpty()) {
//     traverse(res, *tt1, *tt2);
//     tt1 = tt1->next();
//     tt2 = tt2->next();
//     if (res.side_condition != EQUAL) {
//       break;
//     }
//   }
// #if VDEBUG
//   auto cond = res.side_condition;
// #endif
//   traverse(res, tt1, -1);
//   traverse(res, tt2,  1);
//   ASS_EQ(cond, res.side_condition)
// }
//
// int LaKbo::symbolWeight(Term* t) const
// {
//   ASS_REP(tryNumeralMultiplication(t).isNone(), *t)
//   ASS(!t->isLiteral());
//   return KBO::functionWeight(t->functor());
// }
//
// void LaKbo::traverse(TraversalResult& res, TermList tl1_, TermList tl2_) const
// {
//   auto tl1 = dropNumeralMultiplications(res, tl1_);
//   auto tl2 = dropNumeralMultiplications(res, tl2_);
//   if (tl1.isTerm() && tl2.isTerm()) {
//     auto t1 = tl1.term();
//     auto t2 = tl2.term();
//     res.weight_balance -= symbolWeight(t1);
//     res.weight_balance += symbolWeight(t2);
//     if (t1->functor() == t2->functor()) {
//       if (isACFunction(t1->functor())) {
//         traverseAC(res, t1, t2);
//       } else {
//         traverseLex(res, t1->args(), t2->args());
//       }
//     } else {
//       auto prec = KBO::compareFunctionPrecedences(t1->functor(), t2->functor());
//       ASS(prec == LESS || prec == GREATER);
//       res.side_condition = prec;
//       traverse(res, t1->args(), -1);
//       traverse(res, t2->args(),  1);
//     }
//   } else if (tl1.isVar() && tl2.isVar()) {
//     res.addVarBalance(tl1.var(), -1);
//     res.addVarBalance(tl2.var(),  1);
//     res.side_condition = tl1.var() == tl2.var() ? Result::EQUAL : Result::INCOMPARABLE;
//   } else if (tl1.isVar() && tl2.isTerm()) {
//     traverseSubterm(res, tl2.term(), tl1.var(), false);
//   } else {
//     ASS(tl1.isTerm() && tl2.isVar()) 
//     traverseSubterm(res, tl1.term(), tl2.var(), true);
//   }
// }
//
// void LaKbo::TraversalResult::addVarBalance(unsigned var, int amount)
// {
//   CALL("addVarBalance(unsigned var, int amount)")
//   ASS(amount == -1 || amount == 1)
//   auto& bal = this->var_balances.getOrInit(var, [&](){ 
//       this->vars.push(var);
//       return 0; 
//   });
//   bal += amount;
// }
// LaKbo::VarCondition LaKbo::TraversalResult::varCondition() const
// {
//   auto out = VarCondition::Equal;
//   for (auto v : vars) {
//     auto bal = var_balances.get(v);
//     if (bal > 0) {
//       if (out == VarCondition::Equal) {
//         out = VarCondition::RightPlus;
//       } else if(out == VarCondition::LeftPlus) {
//         return VarCondition::BothPlus;
//       } else {
//         ASS_EQ(out, VarCondition::RightPlus)
//       }
//     } else if (bal < 0) {
//       if (out == VarCondition::Equal) {
//         out = VarCondition::LeftPlus;
//       } else if(out == VarCondition::RightPlus) {
//         return VarCondition::BothPlus;
//       } else {
//         ASS_EQ(out, VarCondition::LeftPlus)
//       }
//     }
//   }
//   return out;
// }
//
// LaKbo::Result LaKbo::toOrdering(TraversalResult const& res) const
// {
//   switch (res.varCondition()) {
//     case BothPlus:
//       return Result::INCOMPARABLE;
//
//     case LeftPlus:
//       if (res.weight_balance < 0) {
//         return Result::GREATER;
//       } else if (res.weight_balance > 0  || res.side_condition == EQUAL|| res.side_condition == Result::LESS) {
//         return Result::INCOMPARABLE;
//       } else {
//         ASS_EQ(res.weight_balance, 0)
//         return res.side_condition;
//       }
//
//     case RightPlus:
//       if (res.weight_balance > 0) {
//         return Result::LESS;
//       } else if (res.weight_balance < 0 || res.side_condition == EQUAL || res.side_condition == GREATER) {
//         return Result::INCOMPARABLE;
//       } else {
//         ASS_EQ(res.weight_balance, 0)
//         return res.side_condition;
//       }
//
//     case Equal:
//       if (res.weight_balance < 0) {
//         return Result::GREATER;
//       } else if (res.weight_balance > 0) {
//         return Result::LESS;
//       } else {
//         return res.side_condition;
//       }
//   }
//   ASSERTION_VIOLATION
// }
//
// LaKbo::TraversalResult LaKbo::TraversalResult::initial() 
// {
//   return {
//     .weight_balance = 0,
//     .var_balances = Map<unsigned, int>(),
//     .vars = Stack<unsigned>(),
//     .side_condition = Ordering::EQUAL,
//   };
// }

} // Kernel
