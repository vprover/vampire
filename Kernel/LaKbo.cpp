
#include "LaKbo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"


namespace Kernel {

LaKbo::LaKbo(KBO kbo) : KBO(std::move(kbo))
{

}

struct NumeralMultiplication {
  TermList numeral;
  TermList nonNumeral;
};

template<class NumTraits>
Option<NumeralMultiplication> tryNumeralMultiplication(Term* t)
{
  if (t->functor() == NumTraits::mulF()) {
    for (unsigned i : {0, 1}) {
      if (NumTraits::tryNumeral(*t->nthArgument(i)).isSome()) {
        return Option<NumeralMultiplication>({
            .numeral = *t->nthArgument(i),
            .nonNumeral = *t->nthArgument(1 - i),
        });
      }
    }
  }
  return Option<NumeralMultiplication>();
}

template<class NumTraits>
Option<TermList> _dropNumeralMultiplications(TermList t)
{
  auto nonNumeralPart = [](TermList t) -> Option<TermList> 
    { 
      if (t.isVar()) {
        return Option<TermList>();
      } else {
        return tryNumeralMultiplication<NumTraits>(t.term())
                      .map([](NumeralMultiplication mul){return mul.nonNumeral;}); 
      }
    };
  auto out = nonNumeralPart(t);
  if (out.isSome()) {
    for (auto nonNum = out; nonNum.isSome(); nonNum = nonNumeralPart(nonNum.unwrap())) {
      out = nonNum;
    }
    return out;
  } else {
    return out;
  }
}


TermList LaKbo::dropNumeralMultiplications(LaKbo::TraversalResult& res,  TermList t) const
{
  auto dropped = _dropNumeralMultiplications< IntTraits>(t)
    || [t]() { return _dropNumeralMultiplications< RatTraits>(t); }
    || [t]() { return _dropNumeralMultiplications<RealTraits>(t); };
  if (dropped.isSome()) {
    res.side_condition = INCOMPARABLE;
  }
   return dropped || t;
}

Option<NumeralMultiplication> tryNumeralMultiplication(Term* t)
{
  return tryNumeralMultiplication<IntTraits>(t)
    || [t]() { return tryNumeralMultiplication< RatTraits>(t); }
    || [t]() { return tryNumeralMultiplication<RealTraits>(t); };
}


template<class F>
void LaKbo::traverse(TraversalResult& res, TermList t, int factor, F fun) const
{
  ASS(factor == -1 || factor == 1)
  t = dropNumeralMultiplications(res, t);
  fun(t);
  if (t.isTerm()) {
    auto term = t.term();
    res.weight_balance += factor * symbolWeight(term);
    traverse(res, term->args(), factor, fun);
  } else {
    res.addVarBalance(t.var(), factor);
    res.weight_balance += factor * KBO::variableWeight();
  }
}


void LaKbo::traverse(TraversalResult& res, TermList* tt, int factor) const
{ traverse(res,tt,factor,[](TermList) {} ); }

void LaKbo::traverse(TraversalResult& res, TermList t, int factor) const
{ traverse(res,t,factor,[](TermList) {} ); }

template<class F>
void LaKbo::traverse(TraversalResult& res, TermList* tt, int factor, F fun) const
{
  while (!tt->isEmpty()) {
    traverse(res, *tt, factor, fun);
    tt = tt->next();
  }
}

void LaKbo::traverseSubterm(TraversalResult& res, Term* t, unsigned var, bool varRhs) const
{
  traverse(res, TermList::var(var), varRhs ? 1 : -1);
  traverse(res, TermList(t), varRhs ? -1 : 1, [&](TermList t) { 
      if (t.isVar() && t.var() == var) { 
        /* subterm found */
        res.side_condition = varRhs ? GREATER : LESS;
      } 
    });
}

 
template<class NumTraits>
bool isACFunction(unsigned f) 
{ return f == NumTraits::addF() || f == NumTraits::mulF(); }

bool isACFunction(unsigned f)
{ return isACFunction<IntTraits>(f) || isACFunction<RatTraits>(f) || isACFunction<RealTraits>(f); }
 

void LaKbo::traverseAC(TraversalResult& res, Term* t1, Term* t2) const
{
  auto f = t1->functor();

  traverse(res, t1->args(), -1);
  traverse(res, t2->args(),  1);

  ASS_EQ(t1->functor(), t2->functor());
  ASS(isACFunction(f));

  class Flattened {
    Stack<TermList> _smallFns;
    Stack<TermList> _bigFnsAndVars;
  public:
    Flattened(Flattened &&) = default;
    Flattened(Stack<TermList> small, Stack<TermList> big) 
      : _smallFns(std::move(small))
      , _bigFnsAndVars(std::move(big)) {}

    Stack<TermList>& bigFnsAndVars() { return _bigFnsAndVars; }
    Stack<TermList>& smallFns() { return _smallFns; }
    unsigned size() const { return _bigFnsAndVars.size() + _smallFns.size(); }
  };

  /* flattens ac terms into a stack of their arguments.
     assumes that terms are normalized to (t_1 * (t_2 * (... * t_n))).
     Also it assumes that t_1 < t_2 < t_n wrt std::less<TermList>. */
  auto flatten = [&](Term* t) -> Flattened {
    auto isSmallFn = [&](TermList t) -> bool 
      { return t.isTerm() &&  compareFunctionPrecedences(t.term()->functor(), f) == LESS; };

    auto small = Stack<TermList>{ };
    auto big   = Stack<TermList>{ };

    auto insert = [&](TermList t) {
      ASS(!(t.isTerm() && t.term()->functor() == f));
      (isSmallFn(t) ? small : big).push(t);
    };
    auto cur = TermList(t);
    while (cur.isTerm() && cur.term()->functor() == f) {
      auto l = *cur.term()->nthArgument(0);
      cur = *cur.term()->nthArgument(1);
      insert(l);
    }
    insert(cur);

    return Flattened(std::move(small), std::move(big));
  };

  auto multisetCmp = [&](Stack<TermList>& s1, Stack<TermList>& s2) -> LaKbo::Result
  {
    /* remove equal elements. we assume that s1 and s2 are sorted. */
    unsigned i1 = 0;
    unsigned o1 = 0;
    unsigned i2 = 0;
    unsigned o2 = 0;
    auto keep = [](Stack<TermList>& stack, unsigned& index, unsigned& offset) 
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

    auto checkAllDominated = [this](Stack<TermList> const& s1, Stack<TermList> const& s2) {
      for (auto e1 : s1) {
        if (!iterTraits(s2.iterFifo())
            .find([&](TermList e2) { return compare(e1, e2) == LESS; })
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
      return LESS;
    } else if (dom2) {
      return GREATER;
    } else {
      return INCOMPARABLE;
    }
  };


  auto f1 = flatten(t1);
  auto f2 = flatten(t2);
  auto cmpBig = multisetCmp(f1.bigFnsAndVars(), f2.bigFnsAndVars());
  switch (cmpBig) {
    case LESS:    
    case GREATER: 
    case INCOMPARABLE:
      res.side_condition = cmpBig;
      break;
    case Result::EQUAL:
      if (f1.size() < f2.size()) {
        res.side_condition = Result::LESS;
      } else if (f1.size() > f2.size()) {
        res.side_condition = Result::GREATER;
      } else {
        res.side_condition = multisetCmp(f1.smallFns(), f2.smallFns());
      }
      break;
    default:
      ASSERTION_VIOLATION
  }
}

void LaKbo::traverseLex(TraversalResult& res, TermList* tt1, TermList* tt2) const
{
  while (!tt1->isEmpty()) {
    traverse(res, *tt1, *tt2);
    tt1 = tt1->next();
    tt2 = tt2->next();
    if (res.side_condition != EQUAL)
      break;
  }
#ifdef VDEBUG
  auto cond = res.side_condition;
#endif
  traverse(res, tt1, -1);
  traverse(res, tt2,  1);
  ASS_EQ(cond, res.side_condition)
}

int LaKbo::symbolWeight(Term* t) const
{
  ASS_REP(tryNumeralMultiplication(t).isNone(), *t)
  ASS(!t->isLiteral());
  return KBO::functionWeight(t->functor());
}

void LaKbo::traverse(TraversalResult& res, TermList tl1, TermList tl2) const
{
  tl1 = dropNumeralMultiplications(res, tl1);
  tl2 = dropNumeralMultiplications(res,tl2);
  if (tl1.isTerm() && tl2.isTerm()) {
    auto t1 = tl1.term();
    auto t2 = tl2.term();
    res.weight_balance -= symbolWeight(t1);
    res.weight_balance += symbolWeight(t2);
    if (t1->functor() == t2->functor()) {
      if (isACFunction(t1->functor())) {
        traverseAC(res, t1, t2);
      } else {
        traverseLex(res, t1->args(), t2->args());
      }
    } else {
      auto prec = KBO::compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS(prec == LESS || prec == GREATER);
      res.side_condition = prec;
      traverse(res, t1->args(), -1);
      traverse(res, t2->args(),  1);
    }
  } else if (tl1.isVar() && tl2.isVar()) {
    res.addVarBalance(tl1.var(), -1);
    res.addVarBalance(tl2.var(),  1);
  } else if (tl1.isVar() && tl2.isTerm()) {
    traverseSubterm(res, tl2.term(), tl1.var(), false);
  } else {
    ASS(tl1.isTerm() && tl2.isVar()) 
    traverseSubterm(res, tl1.term(), tl2.var(), true);
  }
}

void LaKbo::TraversalResult::addVarBalance(unsigned var, int amount)
{
  CALL("addVarBalance(unsigned var, int amount)")
  ASS(amount == -1 || amount == 1)
  auto& bal = this->var_balances.getOrInit(var, [&](){ 
      this->vars.push(var);
      return 0; 
  });
  bal += amount;
}
LaKbo::VarCondition LaKbo::TraversalResult::varCondition() const
{
  auto out = VarCondition::Equal;
  for (auto v : vars) {
    auto bal = var_balances.get(v);
    if (bal > 0) {
      if (out == VarCondition::Equal) {
        out = VarCondition::RightPlus;
      } else if(out == VarCondition::LeftPlus) {
        return VarCondition::BothPlus;
      } else {
        ASS_EQ(out, VarCondition::RightPlus)
      }
    } else if (bal < 0) {
      if (out == VarCondition::Equal) {
        out = VarCondition::LeftPlus;
      } else if(out == VarCondition::RightPlus) {
        return VarCondition::BothPlus;
      } else {
        ASS_EQ(out, VarCondition::LeftPlus)
      }
    }
  }
  return out;
}

Literal* normalizeLiteral(Literal* lit) 
{
  Stack<TermList> args(lit->arity());
  for (int i = 0; i < lit->arity(); i++) {
    args.push(normalizeTerm(*lit->nthArgument(i), SortHelper::getArgSort(lit, i)).denormalize());
  }
  return Literal::create(lit, args.begin());
}

LaKbo::Result LaKbo::comparePredicates(Literal* l1, Literal* l2) const 
{
  ASS_EQ(l1->polarity(), l2->polarity());
  l1 = normalizeLiteral(l1);
  l2 = normalizeLiteral(l2);
  auto res = TraversalResult::initial(); 
  if (l1->functor() == l2->functor()) {
    traverseLex(res, l1->args(), l2->args());
  } else {
    res.weight_balance -= predicateWeight(l1->functor());
    traverse(res, l1->args(), -1);
    res.weight_balance += predicateWeight(l2->functor());
    traverse(res, l2->args(),  1);
    res.side_condition = Int::compare(predicatePrecedence(l1->functor()), 
                                      predicatePrecedence(l2->functor())) == Lib::LESS ? Result::LESS : Result::GREATER;
  }
  return toOrdering(res);
}

LaKbo::Result LaKbo::toOrdering(TraversalResult const& res) const
{
  switch (res.varCondition()) {
    case BothPlus:
      return Result::INCOMPARABLE;

    case LeftPlus:
      if (res.weight_balance < 0) {
        return Result::GREATER;
      } else if (res.weight_balance > 0 || res.side_condition == LESS) {
        return Result::INCOMPARABLE;
      } else {
        ASS_EQ(res.weight_balance, 0)
        return res.side_condition;
      }

    case RightPlus:
      if (res.weight_balance > 0) {
        return Result::LESS;
      } else if (res.weight_balance < 0 || res.side_condition == GREATER) {
        return Result::INCOMPARABLE;
      } else {
        ASS_EQ(res.weight_balance, 0)
        return res.side_condition;
      }

    case Equal:
      if (res.weight_balance < 0) {
        return Result::GREATER;
      } else if (res.weight_balance > 0) {
        return Result::LESS;
      } else {
        return res.side_condition;
      }

  }
}

LaKbo::TraversalResult LaKbo::TraversalResult::initial() 
{
  return {
    .weight_balance = 0,
    .var_balances = Map<unsigned, int>(),
    .vars = Stack<unsigned>(),
    .side_condition = Ordering::EQUAL,
  };
}

Ordering::Result LaKbo::compare(TermList t1, TermList t2) const 
{
  auto norm = [](TermList t) { return t.isVar() ? t : normalizeTerm(t.term()).denormalize(); };
  auto res = TraversalResult::initial(); 
  traverse(res, norm(t1), norm(t2));
  return toOrdering(res);
}

void LaKbo::show(ostream& out) const 
{ KBO::show(out); }

Comparison LaKbo::compareFunctors(unsigned fun1, unsigned fun2) const 
{ return KBO::compareFunctors(fun1,fun2); }


} // Kernel
