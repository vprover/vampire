#include "LaLpo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Lib/Option.hpp"
#include "Lib/Metaiterators.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {


LaLpo::LaLpo(Precedence prec) 
  : _prec(std::move(prec))
  , _shared(make_shared(new Kernel::IrcState {
        .normalizer = InequalityNormalizer(), 
        .ordering = this,
        .uwa = env.options->unificationWithAbstraction(),
  }))
{
}

// bool isIrcPredicate(unsigned p) {
//   // return forAnyNumTraits([&](auto numTraits) {
//   //     return p == numTraits.geqF()
//   //         || p == numTraits.greaterF()
//   //         ;
//   // }) || p ==;
// }
bool isPlus(unsigned functor)
{ return forAnyNumTraits([&](auto numTraits) 
    { return numTraits.addF() == functor; }); }

template<class F>
auto flat(TermList t, F f) -> Stack<std::result_of_t<F(TermList)>>
{
  Stack<TermList> work;
  Stack<std::result_of_t<F(TermList)>> out;

  if (t.isTerm() && isPlus(t.term()->functor())) {
    ASS(t.isTerm())
    work.push(t);
    auto sym = t.term()->functor();
    while (!work.isEmpty()) {
      auto t = work.pop();
      if (t.isTerm() && t.term()->functor() == sym) {
        work.push(*t.term()->nthArgument(1));
        work.push(*t.term()->nthArgument(0));
      } else {
        out.push(f(t));
      }
    }

  } else  {
    out.push(f(t));
  }
  return out;
}


Stack<TermList> flat(TermList t)
{
  Stack<TermList> out;
  out.push(t);
  if (t.isTerm()) {
    auto sym = t.term()->functor();
    if (isPlus(sym)) {
      ASS(t.term()->arity() == 2)
      unsigned i = 0;
      while (i < out.size()) {
        if (out[i].isTerm() && out[i].term()->functor() == sym) {
          out.push(*out[i].term()->nthArgument(1));
          out[i] = *out[i].term()->nthArgument(0);
        } else {
          i++;
        }
      }
    }
  }
  return out;
}

using MulExtMemo = DArray<Option<Ordering::Result>>;


template<class Cmp> 
Ordering::Result _mulExt(unsigned lsz, unsigned rsz, Cmp cmp_, Option<MulExtMemo&> memo)
{
  CALL("mulExt")
  memo.andThen([&](auto& memo){
      if (memo.size() == 0) 
        memo = MulExtMemo::initialized(lsz * rsz);
  });
  auto cmp = [&](unsigned i, unsigned j) {
    return memo.match(
        [&](auto& memo) { 
          auto idx = i + j * lsz;
          if (memo[idx].isNone()) {
            memo[idx] = Option<Ordering::Result>(cmp_(i, j));
          } 
          return memo[idx].unwrap();
        },
        [&]() { return cmp_(i,j); });
  };

  auto l = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, lsz));
  auto r = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, rsz));

  // removing duplicates
  for (unsigned il = 0; il < l.size();) {
    auto i = l[il];
    for(unsigned ir = 0; ir < r.size();) {
      auto j = r[ir];
      if (cmp(i, j) == Ordering::Result::EQUAL) {
        l.swapRemove(il);
        r.swapRemove(ir);
        goto continue_outer;
      } else {
        ir++;
      }
    }
    il++;
continue_outer:;
  }


  if (l.size() == 0 && r.size() == 0 ) return Ordering::EQUAL;
  else if (l.size() == 0)              return Ordering::LESS;
  else if (r.size() == 0)              return Ordering::GREATER;
  else {

    if (iterTraits(l.iter())
          .all([&](auto i) { return iterTraits(r.iter())
            .any([&](auto j) 
              { return cmp(i,j) == Ordering::LESS; }); })) {
      return Ordering::LESS;
    } else if (iterTraits(r.iter())
          .all([&](auto j) { return iterTraits(l.iter())
            .any([&](auto i) 
              { return cmp(i,j) == Ordering::GREATER; }); })) {
      return Ordering::GREATER;
    } else {
      // all are incomparable
      return Ordering::INCOMPARABLE;
    }

  }
}


template<class Cmp> 
Ordering::Result mulExt(unsigned lsz, unsigned rsz, Cmp cmp)
{
  MulExtMemo memo;
  return mulExt(lsz, rsz, cmp, memo);
}


template<class Cmp> 
Ordering::Result mulExtWithoutMemo(unsigned lsz, unsigned rsz, Cmp cmp)
{
  return _mulExt(lsz, rsz, cmp, Option<MulExtMemo&>());
}

template<class Cmp> 
Ordering::Result mulExt(unsigned lsz, unsigned rsz, Cmp cmp, MulExtMemo& memo)
{
  return _mulExt(lsz, rsz, cmp, Option<MulExtMemo&>(memo));
}

template<class A, class Cmp> 
Ordering::Result mulExt(Stack<A> const& l, Stack<A> const& r, Cmp cmp)
{ return mulExt(l.size(), r.size(), [&](unsigned i, unsigned j) { return cmp(l[i], r[j]); }); }

enum class Pred { Eq, Neq, Greater, Geq, Uninterpreted };

struct Lit {
  Literal* orig;
  Pred pred;
  auto interpreted() const { return pred != Pred::Uninterpreted; }
  auto sort() const { 
    ASS(interpreted())
    return SortHelper::getArgSort(orig, 0);
  }
  Lit(Literal* l) 
    : orig(l)
    , pred(
        l->functor() == 0 
          ? (l->isPositive() ? Pred::Eq : Pred::Neq)
          : tryNumTraits([&](auto numTraits) { 
                auto f = l->functor();
                return f == numTraits.greaterF() ? Option<Pred>(Pred::Greater)
                     : f == numTraits.    geqF() ? Option<Pred>(Pred::Geq    )
                     : Option<Pred>();
              })
            .unwrapOr(Pred::Uninterpreted)
        ) {}
};

template<class Iter1, class Iter2, class Cmp>
auto lexExt(Iter1 ls, Iter2 rs, Cmp cmp) {
  while (ls.hasNext()) {
    ASS(rs.hasNext())
    auto l = ls.next();
    auto r = rs.next();
    auto c = cmp(l,r);
    if (c != Ordering::Result::EQUAL) 
      return c;
  }
  ASS(!rs.hasNext());
  return Ordering::Result::EQUAL;
}

template<class Cmp>
Ordering::Result chainedCmps(Cmp cmp)
{ return cmp(); }


template<class C1, class C2, class... Cs>
Ordering::Result chainedCmps(C1 c1, C2 c2, Cs... cs)
{
  auto c = c1();
  return c != Ordering::Result::EQUAL ? c : chainedCmps(c2, cs...);
}

// template<class As..., class Cs...>
// Ordering::Result tupleCmp(C1 c1, C2 c2, Cs cs...)
// {
//   auto c = c1();
//   return c != Ordering::Result::EQUAL ? c : chainedCmps(c2, cs...);
// }




template<class A, class... Cs>
Ordering::Result cmpChained(A const& l, A const& r, Cs... cs)
{ return chainedCmps([&](){ return cs(l,r); }...); }

LaLpo::Result LaLpo::compare(Literal* l1_, Literal* l2_) const 
{
  CALL("LaLpo::compare(Literal* l1_, Literal* l2_) const")
  auto l1 = Lit(l1_);
  auto l2 = Lit(l2_);


  if (!l1.interpreted() && l2.interpreted()) {
    return Ordering::Result::GREATER;

  } else if (l1.interpreted() && !l2.interpreted()) {
    return Ordering::Result::LESS;

  } else if (!l1.interpreted() && !l2.interpreted()) {

    if (l1.orig->functor() != l2.orig->functor()) {
      return Ordering::fromComparison(_prec.cmpPred(l1.orig->functor(), l2.orig->functor()));

    } else {
      auto lex = lexExt(argIter(l1.orig), argIter(l2.orig), [&](auto& l, auto& r) { return compare(l,r); } );
      if (lex == Result::EQUAL) {
        return l1.orig->isPositive() == l2.orig->isPositive() 
          ? Result::EQUAL
          : (l1.orig->isPositive() ? Result::LESS 
                                   : Result::GREATER);
      } else {
        return lex;
      }

    }

  } else  {

    ASS(l1.interpreted() && l2.interpreted())
    auto cmpPreds =  [](auto l, auto r) 
    { 
      auto cmpSorts = [](auto l, auto r) {
        return l.sort() == r.sort() ? Result::EQUAL
             : l.sort() <  r.sort() ? Result::LESS
             :                        Result::GREATER;
      };
      auto unsorted = Ordering::fromComparison(Int::compare((int)l.pred, (int)r.pred));
      return unsorted == Ordering::EQUAL ? cmpSorts(l,r) 
                                         : unsorted; 
    };

    auto terms = [](auto s) {
      using Out = Stack<std::pair<TermList, Option<TermList>>>;
      return tryNumTraits([&](auto numTraits) { 
            if (numTraits.sort() == s.sort()) {
             auto sum = *s.orig->nthArgument(0) == numTraits.constantTl(0) 
               ? *s.orig->nthArgument(1) 
               : *s.orig->nthArgument(0);
             return Option<Out>(flat(sum, [&](auto t) { 
                      if (t.isTerm() 
                          && t.term()->functor() == numTraits.mulF()
                          && numTraits.isNumeral(*t.term()->nthArgument(0))) {
                        return make_pair(*t.term()->nthArgument(1), Option<TermList>(*t.term()->nthArgument(0)));
                      } else {
                        return make_pair(t, Option<TermList>());
                      }
                    }));
            } else {
              return Option<Out>();
            }
        })
      || Out {
          make_pair(*s.orig->nthArgument(0), Option<TermList>()), 
          make_pair(*s.orig->nthArgument(1), Option<TermList>()), 
        };
    };

    auto ts1 = terms(l1);
    auto ts2 = terms(l2);
    MulExtMemo memo;

    auto mul = mulExt(ts1.size(), ts2.size(), [&](auto i, auto j) { return compare(get<0>(ts1[i]), get<0>(ts2[j])); }, memo);
    if (mul != Ordering::Result::EQUAL) {
      return mul;

    } else {
      auto mulWithNum = mulExtWithoutMemo(ts1.size(), ts2.size(), 
          [&](auto i, auto j) { 
            auto t1 = get<0>(ts1[i]);
            auto t2 = get<0>(ts2[i]);
            auto n1 = get<1>(ts1[i]);
            auto n2 = get<1>(ts2[i]);

            auto ct = memo[i + ts1.size() * j]
               .unwrapOrInit([&](){ return compare(t1, t2); });
            if (ct != Ordering::EQUAL) return ct;
            else {
              if (n1.isSome() && n2.isSome()) {
                return compare(n1.unwrap(), n2.unwrap());
              } else if (n1.isNone() && n2.isSome()) {
                return Ordering::Result::LESS;
              } else if (n1.isSome() && n2.isNone()) {
                return Ordering::Result::GREATER;
              } else {
                ASS(n1.isNone() && n2.isNone());
                return Ordering::EQUAL;
              }
            }
          });
      return mulWithNum == Ordering::Result::EQUAL 
          ? cmpPreds(l1, l2)
          : mulWithNum;
    }
  }

}



Ordering::Result LaLpo::compare(TermList s, TermList t) const 
{
  auto cmp = [&](TermList s, TermList t) { return compare(s, t); };

  auto case0 = [&](TermList s, TermList t) -> Ordering::Result {
    ASS(s.isVar())
    return t.term()->containsSubterm(s) ? Ordering::Result::LESS
                                : Ordering::Result::INCOMPARABLE;
  };

  auto case1 = [&](TermList s, TermList t, unsigned startIdx) -> bool {
    // CASE 1
    for (unsigned i = startIdx; i < t.term()->arity(); i++) {
      switch (cmp(s, *t.term()->nthArgument(i))) {
        case Ordering::Result::LESS: 
        case Ordering::Result::EQUAL: return true;
        default: break;
      }
    }
    return false;
  };

  auto case1BiDir = [&](TermList s, TermList t, unsigned startIdx) -> Ordering::Result { 
    return case1(s, t, startIdx) ? Ordering::Result::LESS 
         : case1(t, s, startIdx) ? Ordering::Result::GREATER
         : Ordering::Result::INCOMPARABLE;
  };

  auto majo = [&](TermList s, unsigned startIdx, TermList t) -> bool {
      for (unsigned i = startIdx; i < s.term()->arity(); i++) {
        switch (cmp(*s.term()->nthArgument(i), t)) {
          case Ordering::LESS: break;
          default: return false;
        }
      }
      return true;
  };

  auto majoOrCase1 = [&](TermList s, unsigned startIdx, TermList t) -> Ordering::Result {
    return majo(s, startIdx, t)  ? Ordering::Result::LESS 
         : case1(t, s, startIdx) ? Ordering::Result::GREATER
         : Ordering::Result::INCOMPARABLE;
  };


  
  if (s.isVar() && t.isVar()) { return s == t ? Ordering::Result::EQUAL 
                                              : Ordering::Result::INCOMPARABLE; } 
  else if (s.isVar()) { return                   case0(s, t) ; } 
  else if (t.isVar()) { return Ordering::reverse(case0(t, s)); } 
  else {
    ASS(s.isTerm() && t.isTerm())
    auto& s_ = *s.term();
    auto& t_ = *t.term();
    auto f = s_.functor();
    auto g = t_.functor();

    if (isPlus(f) || isPlus(g)) {
      // CASE 2a
      return mulExt(flat(s), flat(t), cmp);

    } else if (f == g) {
      auto arity = s_.arity();
      auto c = Ordering::Result::EQUAL; 
      unsigned i = 0;
      for (; i < arity; i++) {
        c = cmp(*s_.nthArgument(i), *t_.nthArgument(i));
        if (c != EQUAL)  {
          i++;
          break;
        }
      }

      switch (c) {
        case Ordering::Result::EQUAL:        return Ordering::Result::EQUAL;
        // CASE 2b
        case Ordering::Result::LESS:         return      majoOrCase1(s, i, t); // || case1
        // CASE 2b
        case Ordering::Result::GREATER:      return Ordering::reverse(majoOrCase1(t, i, s)); // || case1
        case Ordering::Result::INCOMPARABLE: return case1BiDir(s, t, i);
        default: ASSERTION_VIOLATION
      }
    }  else {
      switch (cmpFun(&s_, &t_)) {
        // CASE 2c
        case Comparison::LESS:    return majoOrCase1(s, 0, t);
        case Comparison::GREATER: return Ordering::reverse(majoOrCase1(t, 0, s));
        case Comparison::EQUAL: /* partial precedence ordering; that's okay */ return case1BiDir(s, t, 0);
      }
    }
  }

}

std::tuple<IntegerConstantType, IntegerConstantType, TermList> toIntPair(IntegerConstantType i)
{ return make_tuple(i, 1, IntegerConstantType::getSort()); }

template<class C>
std::tuple<IntegerConstantType, IntegerConstantType, TermList> toIntPair(C c)
{ return make_tuple(c.numerator(), c.denominator(), C::getSort()); }

Comparison LaLpo::cmpFun(Term* l, Term* r) const
{
  auto f = l->functor();
  auto g = r->functor();
  if (f == g) 
    return Comparison::EQUAL;

  auto lMul = forAnyNumTraits([&](auto numTraits) { return f == numTraits.mulF(); });
  auto rMul = forAnyNumTraits([&](auto numTraits) { return g == numTraits.mulF(); });

  auto lMin = forAnyNumTraits([&](auto numTraits) { return f == numTraits.minusF(); });
  auto rMin = forAnyNumTraits([&](auto numTraits) { return g == numTraits.minusF(); });

  auto lNum = forAnyNumTraits([&](auto numTraits) { return numTraits.tryNumeral(l).map([](auto n){ return  toIntPair(n); }); });
  auto rNum = forAnyNumTraits([&](auto numTraits) { return numTraits.tryNumeral(r).map([](auto n){ return  toIntPair(n); }); });

  auto cmpNums = [&](auto l, auto r) {
    auto ltied = std::tie(get<2>(l),get<1>(l),get<0>(l));
    auto rtied = std::tie(get<2>(r),get<1>(r),get<0>(r));
    //                    ^^sort^^  ^^denom^^ ^^^num^^^
    if (ltied == rtied) return Comparison::EQUAL;
    if (ltied <  rtied) return Comparison::LESS;
    else        return Comparison::GREATER;
  };

  if ( lMin          && !rMin          ) return Comparison::LESS;
  if (!lMin          &&  rMin          ) return Comparison::GREATER;
  if ( lMul          && !rMul          ) return Comparison::LESS;
  if (!lMul          &&  rMul          ) return Comparison::GREATER;
  if ( lNum.isSome() && !rNum.isSome() ) return Comparison::LESS;
  if (!lNum.isSome() &&  rNum.isSome() ) return Comparison::GREATER;
  if ( lNum.isSome() &&  rNum.isSome() ) return cmpNums(lNum.unwrap(), rNum.unwrap());
  else return _prec.cmpFun(f,g);
}

void LaLpo::show(ostream& out) const 
{ _prec.show(out); }

void Precedence::show(ostream& out) const 
{
  CALL("PrecedenceOrdering::show(ostream& out)")
  {
    out << "% Function precedences, smallest symbols first (line format: `<name> <arity>`) " << std::endl;
    out << "% ===== begin of function precedences ===== " << std::endl;
    DArray<unsigned> functors;

    functors.initFromIterator(getRangeIterator(0u,env.signature->functions()),env.signature->functions());
    functors.sort(closureComparator([&](unsigned l, unsigned r){ return cmpFun(l,r); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getFunction(i);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of function precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  {
    out << "% Predicate precedences, smallest symbols first (line format `<name> <arity>`) " << std::endl;
    out << "% ===== begin of predicate precedences ===== " << std::endl;

    DArray<unsigned> functors;
    functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
    functors.sort(closureComparator([&](unsigned l, unsigned r) { return cmpPred(l,r); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getPredicate(i);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of predicate precedences ===== " << std::endl;
  }

  // out << "%" << std::endl;
  //
  // {
  //   out << "% Predicate levels (line format: `<name> <arity> <level>`)" << std::endl;
  //   out << "% ===== begin of predicate levels ===== " << std::endl;
  //
  //   DArray<unsigned> functors;
  //   functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
  //   functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(_predicateLevels[l], _predicateLevels[r]); }));
  //
  //   for (unsigned i = 0; i < functors.size(); i++) {
  //     auto sym = env.signature->getPredicate(i);
  //     out << "% " << sym->name() << " " << sym->arity() << " " << _predicateLevels[i] << std::endl;
  //   }
  //
  //   out << "% ===== end of predicate precedences ===== " << std::endl;
  // }
  //
  // out << "%" << std::endl;
  //
  // showConcrete(out);
}

Comparison Precedence::cmpFun(unsigned l, unsigned r) const 
{ return Int::compare(
    l < _funPrec.size() ? _funPrec[l] : l, 
    r < _funPrec.size() ? _funPrec[r] : r); }

Comparison Precedence::cmpPred(unsigned l, unsigned r) const
{ return Int::compare(
    l < _predPrec.size() ? _predPrec[l] : l, 
    r < _predPrec.size() ? _predPrec[r] : r); }

Precedence Precedence::random() 
{
  Precedence out(
      DArray<int>::fromIterator(getRangeIterator<int>(0, env.signature-> functions())),
      DArray<int>::fromIterator(getRangeIterator<int>(0, env.signature->predicates())));
  auto rng = [](int i) -> int { return Random::getInteger() % i; };
  std::random_shuffle(out. _funPrec.begin(), out. _funPrec.end(), rng);
  std::random_shuffle(out._predPrec.begin(), out._predPrec.end(), rng);
  return out;
}

} // Kernel
