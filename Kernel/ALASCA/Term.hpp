/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Term__
#define __ALASCA_Term__

#include "Kernel/NumTraits.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
#include "Lib/VirtualIterator.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

#define DECL_LIN_MUL_OPS(Type) \
    friend Type operator/(Type const& t, Numeral n) { return n.inverse() * t; } \
    friend Type operator/(Type const& t, int n) { return t / Numeral(n); } \
    friend Type operator*(int n, Type const& t) { return Numeral(-1) * t; } \
    Type operator-() const { return -1 * *this; } \

namespace Kernel {

#define OPS_FROM_TO_TERM(Type) \
  auto asTuple() const { return std::tuple(toTerm()); } \
  IMPL_COMPARISONS_FROM_TUPLE(Type) \
  IMPL_HASH_FROM_TUPLE(Type) \
  friend std::ostream& operator<<(std::ostream& out, Type const& self) { return out << self.toTerm(); } \

  /* T can be either TermList or TermSpec */
  struct __AlascaTermApplUF {
    TypedTermList _self;
    __AlascaTermApplUF(TypedTermList t) : _self(t) {}
    TypedTermList toTerm() const { return _self; }
    static __AlascaTermApplUF normalize(Term* t);
    OPS_FROM_TO_TERM(__AlascaTermApplUF);
  };


  template<class NumTraits>
  class AlascaMonom {
    using Numeral = typename NumTraits::ConstantType;
    using ASig = AlascaSignature<NumTraits>;
    Numeral _numeral;
    // TODO make this an Option<TermList>
    TermList _term;
  public:

    AlascaMonom(Numeral numeral, TermList term) 
      : _numeral(std::move(numeral))
      , _term(std::move(term)) 
    {  
      ASS(ASig::one() == _term || !ASig::isNumeral(_term))
    }

    AlascaMonom(Numeral numeral) 
      : AlascaMonom(numeral, NumTraits::one()) 
    {  }

    bool isNumeral() const { return ASig::one() == _term; }
    Option<bool> tryNumeral() const;

    AlascaMonom(int numeral, TermList term) : AlascaMonom(Numeral(numeral), term) {}

    friend AlascaMonom operator*(Numeral const& n, AlascaMonom const& self) { return AlascaMonom(self.numeral() * n, self.atom()); }
    DECL_LIN_MUL_OPS(AlascaMonom)

    Numeral const& numeral() const { return _numeral; }
    TermList const& atom() const { return _term; }

    template<class N>
    friend class __AlascaTermApplNum;
    TypedTermList toTerm() const { return TypedTermList(ASig::linMul(_numeral, _term), NumTraits::sort()); }

    auto asTuple() const { return std::tie(_term, _numeral); }
    IMPL_COMPARISONS_FROM_TUPLE(AlascaMonom)
    IMPL_HASH_FROM_TUPLE(AlascaMonom)
    friend std::ostream& operator<<(std::ostream& out, AlascaMonom const& self) 
    { return out << self._numeral << " " << self._term; }
  };


  /* T can be either TermList or TermSpec */
  template<class NumTraits>
  class __AlascaTermApplNum {
    // TODO set the normalized cache of this term appropriately, so it doesn't have to be re-normalized
    mutable Option<TypedTermList> _self;
    using Numeral = typename AlascaSignature<NumTraits>::Numeral;
    // TODO small size optimization
    Stack<AlascaMonom<NumTraits>> _sum;

    __AlascaTermApplNum(Stack<AlascaMonom<NumTraits>> self) : _sum(std::move(self)) {}
  public:
    template<class Iter>
    static __AlascaTermApplNum fromCorrectlySortedIter(Iter iter) 
    { return __AlascaTermApplNum(iter.template collect<Stack>()); }

    unsigned nSummands() const { return _sum.size(); }
    auto& monomAt(unsigned i) const { return _sum[i]; }
    static __AlascaTermApplNum normalize(Term* t);
    auto iterSummands() const { return arrayIter(_sum); }
    TypedTermList toTerm() const { return _self.unwrapOrInit([&]() -> TypedTermList { 
        return TypedTermList(NumTraits::sum(arrayIter(_sum).map([](auto& m) { return TermList(m.toTerm()); })), NumTraits::sort()); }); 
    }
    OPS_FROM_TO_TERM(__AlascaTermApplNum);
  };

  class __AlascaTermVar {
    TypedTermList _self;
    __AlascaTermVar(TypedTermList t) : _self(t) { ASS(_self.isVar()) }
  public:
    TermList sort() const { return _self.sort(); }
    static __AlascaTermVar normalize(TypedTermList t) { return __AlascaTermVar(t); }
    TypedTermList toTerm() const { return _self; }
    OPS_FROM_TO_TERM(__AlascaTermVar);
  };


  class AlascaTermCache {
    using Inner = Coproduct<__AlascaTermApplUF
      , __AlascaTermApplNum<IntTraits>
      , __AlascaTermApplNum<RatTraits>
      , __AlascaTermApplNum<RealTraits>
      >;
    Inner _self;
    AlascaTermCache(Inner inner) : _self(std::move(inner)) {}
  public:
    friend struct AlascaTermImpl;
    static AlascaTermCache normalizeUF(Term* t)
    { return AlascaTermCache(Inner(__AlascaTermApplUF::normalize(t))); }

    template<class NumTraits>
    static AlascaTermCache normalizeNum(Term* t) 
    { return AlascaTermCache(Inner(__AlascaTermApplNum<NumTraits>::normalize(t))); }

    TypedTermList toTerm() const { return _self.apply([](auto& self) { return self.toTerm(); }); }
    OPS_FROM_TO_TERM(AlascaTermCache);
  };

  
  /* an alasca term of numerals sort NumTraits */
  template<class NumTraits>
  class AlascaTermNum {
    using Appl = __AlascaTermApplNum<NumTraits>;
    using Var = __AlascaTermVar;
    // the internal representation is either a `Var` a variable together with a sort annotation, or an applcation term `Appl`
    // Appl terms are cached for each Term*, thus they are present as a Pointer (Appl*), while variables cannot be cached, 
    // thus they are plain owned data
    using Inner = Coproduct<Appl*, Var>;
    Inner _self;
    template<class C> AlascaTermNum(C inner) : _self(std::move(inner)) {}
    friend struct AlascaTermImpl;
  public:
    static AlascaTermNum fromVar(TypedTermList v)  
    { 
      ASS_EQ(v, NumTraits::sort())
      ASS(v.isVar())
      return AlascaTermNum(__AlascaTermVar::normalize(v)); 
    }

    template<class Iter>
    static AlascaTermNum fromCorrectlySortedIter(Iter iter)
    {
      ASS(iter.knowsSize()) 
      auto create = [&]() {
        if (iter.size() == 1) {
          auto v = iter.next();
          if (v.atom().isVar() && v.numeral() == 1) {
            return fromVar(TypedTermList(v.atom(), NumTraits::sort()));
          } else {
            return AlascaTermNum(move_to_heap(__AlascaTermApplNum<NumTraits>::fromCorrectlySortedIter(iterItems(std::move(v)))));
          }
        } else {
          return AlascaTermNum(move_to_heap(__AlascaTermApplNum<NumTraits>::fromCorrectlySortedIter(std::move(iter))));
        }
      };
      auto out = create();
      out.integrity();
      return out;
    }
    using Numeral = typename NumTraits::ConstantType;

    // TODO

    friend AlascaTermNum operator*(Numeral const& n, AlascaTermNum const& self) 
    { return AlascaTermNum::fromCorrectlySortedIter(self.iterSummands()
          .map([&](auto m) { return n * m; })); }

    DECL_LIN_MUL_OPS(AlascaTermNum)

    unsigned nSummands() const { return _self.match(
        [](Appl* const& x) { return x->nSummands(); },
        [](Var   const& x) { return unsigned(1); }
        ); }

    auto iterSummands() const { return coproductIter(_self.map(
        [](Appl* const& x) { return x->iterSummands().map([](auto& monom) { return monom; }); },
        [](Var   const& x) { return iterItems(AlascaMonom<NumTraits>(1, x.toTerm())); }
        )); }

    TypedTermList toTerm() const { return _self.match(
        [](Appl* const& x) { return x->toTerm(); },
        [](Var   const& x) { return x.toTerm(); }
        ); }

    AlascaMonom<NumTraits> summandAt(unsigned i) const { return _self.match(
        [&](Appl* const& x) { return x->monomAt(i); },
        [&](Var   const& x) { ASS_EQ(i, 0); return AlascaMonom<NumTraits>(1, x.toTerm()); }
        ); }

    void integrity() { DEBUG_CODE(
      auto iter = iterSummands();
      if (iter.hasNext())  {
        auto x1 = iter.next();
        while (iter.hasNext()) {
          auto x2 = iter.next();
          ASS(x1.atom() < x2.atom());
          x1 = x2;
        }
      }
      for (auto x : iterSummands()) {
        ASS(x.numeral() != 0)
      }
    ) }

    OPS_FROM_TO_TERM(AlascaTermNum);
  };

  using AlascaTermNumAny  = Coproduct<
        AlascaTermNum<IntTraits>
      , AlascaTermNum<RealTraits>
      , AlascaTermNum<RatTraits>
      >;

  struct AlascaTermImpl {
    template<class NumTraits>
    static Option<AlascaTermNumAny> asSum(__AlascaTermApplNum<NumTraits>* const& t) 
    { return some(AlascaTermNumAny(AlascaTermNum<NumTraits>(t))); }

    static Option<AlascaTermNumAny> asSum(__AlascaTermApplUF* const& t) 
    { 
      forEachNumTraits([&](auto n) { ASS_NEQ(t->toTerm().sort(), n.sort()) });
      return {};
    }

    static Option<AlascaTermNumAny> asSum(AlascaTermCache* const& t) 
    { return t->_self.apply([](auto& x) { return asSum(&x); }); }

    static Option<AlascaTermNumAny> asSum(__AlascaTermVar const& t) 
    { 
      return tryNumTraits([&](auto n){
          return someIf(n.sort() == t.sort(), 
              [&]() { return AlascaTermNumAny(AlascaTermNum<decltype(n)>::fromVar(t.toTerm())); });
      });
    }
  };

  // TODO rename to AlascaTerm
  class AnyAlascaTerm 
  { 
    using Inner = Coproduct< __AlascaTermVar
                           , AlascaTermCache*>;
    Inner _self;

    AnyAlascaTerm(Inner inner) : _self(std::move(inner)) {}
  public:
    static AnyAlascaTerm normalize(TypedTermList t) {
      if (t.isVar()) {
        return AnyAlascaTerm(Inner(__AlascaTermVar::normalize(t)));
      } else {
        if (t.term()->getAlascaTermCache() == nullptr) {
          auto term = t.term();
          auto computeNormalization = [&]() {
            auto sort = t.sort();
            return 
              forAnyNumTraits([&](auto n) -> Option<AlascaTermCache> {
                  if (n.sort() != sort) return {};
                  return some(AlascaTermCache(AlascaTermCache::normalizeNum<decltype(n)>(term)));
              })
              .unwrapOrElse([&]() { return AlascaTermCache::normalizeUF(term); });
          };
          t.term()->setAlascaTermCache(move_to_heap(computeNormalization()));
        }
        return AnyAlascaTerm(Inner(t.term()->getAlascaTermCache()));
      }
    }

    TypedTermList toTerm() const
    { return _self.match([&](auto& owned) { return owned.toTerm(); }
                        ,[&](auto& ptr  ) { return ptr->toTerm(); }); }
    
    Option<AlascaTermNumAny> asSum() const 
    { return _self.apply([](auto& x) { return AlascaTermImpl::asSum(x); }); }
    
    Option<AlascaTermNumAny> asNonTrivialSum() const;

    IterTraits<VirtualIterator<AnyAlascaTerm>> iterSubterms() const;
    
    template<class NumTraits> Option<AlascaTermNum<NumTraits>> asSum() const 
    { return asSum().andThen([](auto x) {
          return x.template as<AlascaTermNum<NumTraits>>().toOwned(); }); }

    template<class NumTraits> Option<AlascaTermNum<NumTraits>> asNonTrivalSum() const 
    { return asNonTrivialSum().andThen([](auto x) {
          return x.template as<AlascaTermNum<NumTraits>>().toOwned(); }); }

    OPS_FROM_TO_TERM(AnyAlascaTerm);
  };

  inline __AlascaTermApplUF __AlascaTermApplUF::normalize(Term* t) {
    return __AlascaTermApplUF(TypedTermList(Term::createFromIter(t->functor(), concatIters(
          typeArgIter(t),
          termArgIterTyped(t)
            .map([](auto t) { return AnyAlascaTerm::normalize(t).toTerm(); })))));
  }

  template<class NumTraits>
  __AlascaTermApplNum<NumTraits> __AlascaTermApplNum<NumTraits>::normalize(Term* t) {
    using ASig = AlascaSignature<NumTraits>;

    using Monom = AlascaMonom<NumTraits>;
    Stack<Monom> done;
    RStack<Monom> todo;
    todo->push(Monom(1, TermList(t)));
    while (todo->isNonEmpty()) {
      auto next = todo->pop();

      optionIfThenElse(
          [&]() { return NumTraits::ifAdd([&](auto l, auto r) {
            todo->push(Monom(next.numeral(), l));
            todo->push(Monom(next.numeral(), r));
            }); },
          [&]() { return ASig::ifNumMul([&](auto k, auto t) {
            todo->push(Monom(next.numeral() * k, t));
            }); },
          [&]() { return ASig::ifNumeral([&](auto k) {
            todo->push(Monom(next.numeral() * k));
            }); },
          [&]() { 
            if (next.numeral() != 0) {
              auto inner = AnyAlascaTerm::normalize(TypedTermList(next.atom(), NumTraits::sort()))
                        .template asSum<NumTraits>()
                        .unwrap();
              for (auto m : inner.iterMonoms()) {
                done->push(Monom(next.numeral(), m));
              }
            }
          });
    }

    /* summing up */
    if (done.size() != 0) {
      done.sort([](auto& l, auto& r) { return l.atom() < r.atom(); });
      auto sz = 0;
      auto i = 0;
      while (i < done.size()) {
        ASS_L(sz, i)
        if (done[sz].atom() == done[i].atom()) {
          done[sz]._numeral += done[i].numeral();
          i++;
        } else {
          ASS(done[sz].atom() < done[i].atom())
          if (done[sz].numeral() == 0) {
            done[sz] = done[i];
            i++;
          } else {
            sz++;
            done[sz] = done[i];
            i++;
          }
        }
      }
      if (done[sz].numeral() != 0) {
        sz++;
      }
      done.pop(done.size() - sz);
    }

    return __AlascaTermApplNum<NumTraits>(std::move(done));
  }

} // namespace Kernel

#undef DEBUG
#undef DECL_LIN_MUL_OPS
 
#endif // __ALASCA_Term__


