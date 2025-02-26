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

#include "Kernel/Term.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
#include "Lib/VirtualIterator.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Kernel {


#define OPS_FROM_TO_TERM(Type) \
  auto asTuple() const { return std::tuple(toTerm()); } \
  IMPL_COMPARISONS_FROM_TUPLE(Type) \
  IMPL_HASH_FROM_TUPLE(Type) \
  friend std::ostream& operator<<(std::ostream& out, Type const& self) { return out << self.toTerm(); } \

  /* T can be either TermList or TermSpec */
  class AlascaTermApplUF {
    TermList _self;
    AlascaTermApplUF(TermList t) : _self(t) {}
  public:
    TermList toTerm() const { return _self; }
    static AlascaTermApplUF normalize(Term* t);
    OPS_FROM_TO_TERM(AlascaTermApplUF);
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

    friend AlascaMonom operator*(Numeral n, AlascaMonom const& self) { return AlascaMonom(self.numeral() * n, self.atom()); }
    friend AlascaMonom operator*(int n, AlascaMonom const& t) { return Numeral(-1) * t; }
    friend AlascaMonom operator/(AlascaMonom const& t, Numeral n) { return n.inverse() * t; }
    friend AlascaMonom operator/(AlascaMonom const& t, int n) { return *t / Numeral(n); }
    AlascaMonom operator-() const { return -1 * *this; }

    Numeral const& numeral() const { return _numeral; }
    TermList const& atom() const { return _term; }

    template<class N>
    friend class AlascaTermApplNum;
    TermList toTerm() const { return ASig::linMul(_numeral, _term); }

    auto asTuple() const { return std::tie(_term, _numeral); }
    IMPL_COMPARISONS_FROM_TUPLE(AlascaMonom)
    IMPL_HASH_FROM_TUPLE(AlascaMonom)
    friend std::ostream& operator<<(std::ostream& out, AlascaMonom const& self) 
    { return out << self._numeral << " " << self._term; }
  };




  /* T can be either TermList or TermSpec */
  template<class NumTraits>
  class AlascaTermApplNum {
    // TODO set the normalized cache of this term appropriately, so it doesn't have to be re-normalized
    mutable Option<TermList> _self;
    using Numeral = typename AlascaSignature<NumTraits>::Numeral;
    // TODO small size optimization
    Stack<AlascaMonom<NumTraits>> _sum;

    AlascaTermApplNum(Stack<AlascaMonom<NumTraits>> self) : _sum(std::move(self)) {}
  public:


    unsigned nSummands() const { return _sum.size(); }
    auto& monomAt(unsigned i) const { return _sum[i]; }
    static AlascaTermApplNum normalize(Term* t);
    auto iterSummands() const { return arrayIter(_sum); }
    TermList toTerm() const { return _self.unwrapOrInit([&]() -> TermList { return NumTraits::sum(arrayIter(_sum).map([](auto& m) { return m.toTerm(); })); }); }
    OPS_FROM_TO_TERM(AlascaTermApplNum);
  };

  class AlascaTermVar {
    TypedTermList _self;
    AlascaTermVar(TypedTermList t) : _self(t) { ASS(_self.isVar()) }
  public:
    static AlascaTermVar normalize(TypedTermList t) { return AlascaTermVar(t); }
    TermList toTerm() const { return _self; }
    OPS_FROM_TO_TERM(AlascaTermVar);
  };


  class AlascaTermAppl {
    using Inner = Coproduct<AlascaTermApplUF
      , AlascaTermApplNum<IntTraits>
      , AlascaTermApplNum<RatTraits>
      , AlascaTermApplNum<RealTraits>
      >;
    Inner _self;
    AlascaTermAppl(Inner inner) : _self(std::move(inner)) {}
  public:
    static AlascaTermAppl normalizeUF(Term* t)
    { return AlascaTermAppl(Inner(AlascaTermApplUF::normalize(t))); }
    template<class NumTraits>
    static AlascaTermAppl normalizeNum(Term* t) 
    { return AlascaTermAppl(Inner(AlascaTermApplNum<NumTraits>::normalize(t))); }
    TermList toTerm() const { return _self.apply([](auto& self) { return self.toTerm(); }); }
    OPS_FROM_TO_TERM(AlascaTermAppl);
  };
  
  /* an alasca term of numerals sort NumTraits */
  template<class NumTraits>
  class AlascaTermNum {
    using Appl = AlascaTermApplNum<NumTraits>;
    using Var = AlascaTermVar;
    // the internal representation is either a `Var` a variable together with a sort annotation, or an applcation term `Appl`
    // Appl terms are cached for each Term*, thus they are present as a Pointer (Appl*), while variables cannot be cached, 
    // thus they are plain owned data
    using Inner = Coproduct<Appl*, Var>;
    Inner _self;


    AlascaTermNum(Inner inner) : _self(std::move(inner)) {}
  public:
    template<class Iter>
    static AlascaTermNum fromCorrectlySortedIter(Iter iter);
    using Numeral = typename NumTraits::ConstantType;

    // TODO
    friend AlascaTermNum operator*(Numeral n, AlascaTermNum const&);

    friend AlascaTermNum operator/(AlascaTermNum const& t, Numeral n) { return n.inverse() * t; }
    friend AlascaTermNum operator/(AlascaTermNum const& t, int n) { return t / Numeral(n); }
    friend AlascaTermNum operator*(int n, AlascaTermNum const& t) { return Numeral(-1) * t; }
    AlascaTermNum operator-() const { return -1 * *this; }

    unsigned nSummands() const { return _self.match(
        [](Appl* const& x) { return x->nSummands(); },
        [](Var   const& x) { return unsigned(1); }
        ); }

    auto iterSummands() const { return coproductIter(_self.map(
        [](Appl* const& x) { return x->iterSummands().map([](auto& monom) { return monom; }); },
        [](Var   const& x) { return iterItems(AlascaMonom<NumTraits>(1, x.toTerm())); }
        )); }

    TermList toTerm() const { return _self.match(
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

  // TODO rename to AlascaTerm
  class AnyAlascaTerm 
  { 
    using Inner = Coproduct< AlascaTermVar
                           , AlascaTermAppl*>;
    Inner _self;

    AnyAlascaTerm(Inner inner) : _self(std::move(inner)) {}
  public:
    static AnyAlascaTerm normalize(TypedTermList t) {
      if (t.isVar()) {
        return AnyAlascaTerm(Inner(AlascaTermVar::normalize(t)));
      } else {
        if (t.term()->getAlascaNormalform() == nullptr) {
          auto term = t.term();
          auto computeNormalization = [&]() {
            auto sort = t.sort();
            return 
              forAnyNumTraits([&](auto n) -> Option<AlascaTermAppl> {
                  if (n.sort() != sort) return {};
                  return some(AlascaTermAppl(AlascaTermAppl::normalizeNum<decltype(n)>(term)));
              })
              .unwrapOrElse([&]() { return AlascaTermAppl::normalizeUF(term); });
          };
          t.term()->setAlascaNormalform(move_to_heap(computeNormalization()));
        }
        return AnyAlascaTerm(Inner(t.term()->getAlascaNormalform()));
      }
    }

    TermList toTerm() const
    { return _self.match([&](auto& owned) { return owned.toTerm(); }
                        ,[&](auto& ptr  ) { return ptr->toTerm(); }); }
    
    Option<AlascaTermNumAny> asSum() const;
    
    Option<AlascaTermNumAny> asNonTrivialSum() const;

    IterTraits<VirtualIterator<AnyAlascaTerm>> iterSubterms() const;
    
    template<class NumTraits> Option<AlascaTermNum<NumTraits>> asSum() const;
    template<class NumTraits> Option<AlascaTermNum<NumTraits>> asNonTrivalSum() const;

    OPS_FROM_TO_TERM(AnyAlascaTerm);
  };

  inline AlascaTermApplUF AlascaTermApplUF::normalize(Term* t) {
    return AlascaTermApplUF(TermList(Term::createFromIter(t->functor(), concatIters(
          typeArgIter(t),
          termArgIterTyped(t)
            .map([](auto t) { return AnyAlascaTerm::normalize(t).toTerm(); })))));
  }

  template<class NumTraits>
  AlascaTermApplNum<NumTraits> AlascaTermApplNum<NumTraits>::normalize(Term* t) {
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

    return AlascaTermApplNum<NumTraits>(std::move(done));
  }

} // namespace Kernel

#undef DEBUG
 
#endif // __ALASCA_Term__


