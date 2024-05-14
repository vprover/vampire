#include "LaLpo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Lib/Option.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/OrderingUtils.hpp"
#include <random>

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {


LaLpo::LaLpo(Precedence prec) 
  : _prec(std::move(prec))
  , _shared(nullptr)
{
}

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


template<class Cmp>
Ordering::Result chainedCmps(Cmp cmp)
{ return cmp(); }


template<class C1, class C2, class... Cs>
Ordering::Result chainedCmps(C1 c1, C2 c2, Cs... cs)
{
  auto c = c1();
  return c != Ordering::Result::EQUAL ? c : chainedCmps(c2, cs...);
}

template<class A, class... Cs>
Ordering::Result cmpChained(A const& l, A const& r, Cs... cs)
{ return chainedCmps([&](){ return cs(l,r); }...); }

LaLpo::Result LaLpo::compare(Literal* l1_, Literal* l2_) const 
{
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
      auto lex = OrderingUtils::lexExt(termArgIter(l1.orig), termArgIter(l2.orig), [&](auto& l, auto& r) { return compare(l,r); } );
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
                        return std::make_pair(*t.term()->nthArgument(1), Option<TermList>(*t.term()->nthArgument(0)));
                      } else {
                        return std::make_pair(t, Option<TermList>());
                      }
                    }));
            } else {
              return Option<Out>();
            }
        })
      || Out {
          std::make_pair(*s.orig->nthArgument(0), Option<TermList>()), 
          std::make_pair(*s.orig->nthArgument(1), Option<TermList>()), 
        };
    };

    auto ts1 = terms(l1);
    auto ts2 = terms(l2);
    OrderingUtils::MulExtMemo memo;

    auto mul = OrderingUtils::mulExt(ts1.size(), ts2.size(), [&](auto i, auto j) { return compare(std::get<0>(ts1[i]), std::get<0>(ts2[j])); }, memo);
    if (mul != Ordering::Result::EQUAL) {
      return mul;

    } else {
      auto mulWithNum = OrderingUtils::mulExtWithoutMemo(ts1.size(), ts2.size(), 
          [&](auto i, auto j) { 
            auto t1 = std::get<0>(ts1[i]);
            auto t2 = std::get<0>(ts2[i]);
            auto n1 = std::get<1>(ts1[i]);
            auto n2 = std::get<1>(ts2[i]);

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



Ordering::Result LaLpo::compare(AppliedTerm s, AppliedTerm t) const 
{
  ASSERTION_VIOLATION // TODO
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
      return OrderingUtils::mulExt(flat(s), flat(t), cmp);

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
      ASSERTION_VIOLATION
    }
  }
}

std::tuple<IntegerConstantType, IntegerConstantType, TermList> toIntPair(IntegerConstantType i)
{ return std::make_tuple(i, IntegerConstantType(1), IntegerConstantType::getSort()); }

template<class C>
std::tuple<IntegerConstantType, IntegerConstantType, TermList> toIntPair(C c)
{ return std::make_tuple(c.numerator(), c.denominator(), C::getSort()); }

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
    auto ltied = std::tie(std::get<2>(l),std::get<1>(l),std::get<0>(l));
    auto rtied = std::tie(std::get<2>(r),std::get<1>(r),std::get<0>(r));
    //                    ^^^^^^^sort^^  ^^^^^^^denom^^ ^^^^^^^^num^^^
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

void LaLpo::show(std::ostream& out) const 
{ _prec.show(out); }

void Precedence::show(std::ostream& out) const 
{
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
  auto rng = std::minstd_rand(Random::getInteger( /* arbitrary modulus .. change it as u please */ 65536));
  std::shuffle(out. _funPrec.begin(), out. _funPrec.end(), rng);
  std::shuffle(out._predPrec.begin(), out._predPrec.end(), rng);
  return out;
}

} // Kernel
