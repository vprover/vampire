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

template<class A, class Cmp> 
Ordering::Result mulExt(Stack<A> const& l_, Stack<A> const& r_, Cmp cmp_)
{
  CALL("mulExt")
  auto memo = DArray<Option<Ordering::Result>>::initialized(l_.size() * r_.size());
  auto cmp = [&](unsigned i, unsigned j) {
    auto idx = i + j * l_.size();
    if (memo[idx].isNone()) {
      memo[idx] = Option<Ordering::Result>(cmp_(l_[i], r_[j]));
    } 
    return memo[idx].unwrap();
  };

  auto l = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, l_.size()));
  auto r = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, r_.size()));

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
      if (forAnyNumTraits([&](auto numTraits) { return numTraits.sort() == s.sort(); })) {
        return flat(*s.orig->nthArgument(0));
      } else {
        return Stack<TermList> {*s.orig->nthArgument(0), *s.orig->nthArgument(1)};
      }
    };

    auto mul = mulExt(terms(l1), terms(l2), [&](auto& l, auto& r) { return compare(l,r); });
    return mul == Ordering::Result::EQUAL 
      ? cmpPreds(l1, l2)
      : mul;
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

Comparison LaLpo::cmpFun(Term* l, Term* r) const
{
  auto f = l->functor();
  auto g = r->functor();
  if (f == g) 
    return Comparison::EQUAL;

  auto lMul = forAnyNumTraits([&](auto numTraits) { return f == numTraits.mulF(); });
  auto rMul = forAnyNumTraits([&](auto numTraits) { return g == numTraits.mulF(); });

  auto lNum = forAnyNumTraits([&](auto numTraits) { return numTraits.isNumeral(l); });
  auto rNum = forAnyNumTraits([&](auto numTraits) { return numTraits.isNumeral(r); });

  return  lMul && !rMul ? Comparison::LESS
       : !lMul &&  rMul ? Comparison::GREATER
       :  lNum && !rNum ? Comparison::LESS
       : !lNum &&  rNum ? Comparison::GREATER
       : _prec.cmpFun(f,g);
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

} // Kernel
