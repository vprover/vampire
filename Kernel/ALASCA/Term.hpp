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
// TODO remove(?)

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Kernel {

  /* T can be either TermList or TermSpec */
  class AlascaTermApplUF {
    TermList _self;
    AlascaTermApplUF(TermList t) : _self(t) {}
  public:
    TermList toTerm() const { return _self; }
    static AlascaTermApplUF normalize(Term* t);
  };


  template<class NumTraits>
  struct AlascaMonom {
    using Numeral = typename NumTraits::ConstantType;
    using ASig = AlascaSignature<NumTraits>;
    Numeral numeral;
    TermList term;

  private:
    template<class N>
    friend class AlascaTermApplNum;
    TermList toTerm() const { return ASig::linMul(numeral, term); }
  };


  /* T can be either TermList or TermSpec */
  template<class NumTraits>
  class AlascaTermApplNum {
    mutable Option<TermList> _self;
    using Numeral = typename AlascaSignature<NumTraits>::Numeral;
    // TODO small size optimization
    Stack<AlascaMonom<NumTraits>> _sum;

    AlascaTermApplNum(Stack<AlascaMonom<NumTraits>> self) : _sum(std::move(self)) {}
  public:
    static AlascaTermApplNum normalize(Term* t);
    TermList toTerm() const { return _self.unwrapOrInit([&]() -> TermList { return NumTraits::sum(arrayIter(_sum).map([](auto& m) { return m.toTerm(); })); }); }
  };

  class AlascaTermVar {
    TypedTermList _self;
    AlascaTermVar(TypedTermList t) : _self(t) { ASS(_self.isVar()) }
  public:
    static AlascaTermVar normalize(TypedTermList t) { return AlascaTermVar(t); }
    TermList toTerm() const { return _self; }
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
  };

  /* an alasca term of numerals sort NumTraits */
  template<class NumTraits>
  class AlascaTermNum {
    using Appl = AlascaTermApplNum<NumTraits>;
    using Var = AlascaTermVar;
    // the internal representation is either a `Var` a variable together with a sort annotation, or an applcation term `Appl`
    // Appl terms are cached for each Term*, thus they are present as a Pointer (Appl*), while variables cannot be cached, 
    // thus they are plain owned data
    using Inner = Coproduct<Var, Appl*>;
    Inner _self;

    AlascaTermNum(Inner inner) : _self(std::move(inner)) {}
    static auto iterSummands(Appl*& x)  { return ; }
    static auto iterSummands(Var& x)  { return ; }
  public:

    unsigned nSummands() const { return _self.match(
        [](Appl* const& x) { return x->nSummands(); },
        [](Var   const& x) { return unsigned(1); }
        ); }

    unsigned iterSummands() const { return coproductIter(_self.map(
        [](Appl* const& x) { return x->iterSummands(); },
        [](Var   const& x) { return iterItems(AlascaMonom<NumTraits> { .term = x.toTerm(), .numeral = 1 }); }
        )); }

    TermList toTerm() const { return _self.match(
        [](Appl* const& x) { return x->toTerm(); },
        [](Var   const& x) { return x.toTerm(); }
        ); }

    AlascaMonom<NumTraits> summandAt() const { return _self.match(
        [](Appl* const& x) { return x->monomAt(x); },
        [](Var   const& x) { return AlascaMonom<NumTraits> { .term = x.toTerm(), .numeral = 1 }; }
        ); }

    void integrity() { DEBUG_CODE(
      auto iter = iterSummands();
      if (iter.hasNext())  {
        auto x1 = iter.next();
        while (iter.hasNext()) {
          auto x2 = iter.next();
          ASS(x1.term < x2.term);
          x1 = x2;
        }
      }
      for (auto x : iterSummands()) {
        ASS(x.numeral != 0)
      }
    ) }
  };

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
    
    template<class NumTraits>
    Option<AlascaTermNum<NumTraits>> downcast() const;
  };

  inline AlascaTermApplUF AlascaTermApplUF::normalize(Term* t) {
    return AlascaTermApplUF(TermList(Term::createFromIter(t->functor(), concatIters(
          typeArgIter(t),
          termArgIterTyped(t)
            .map([](auto t) { return AnyAlascaTerm::normalize(t).toTerm(); })))));
  }

  template<class NumTraits>
  AlascaTermApplNum<NumTraits> AlascaTermApplNum<NumTraits>::normalize(Term* t) {

    using Monom = AlascaMonom<NumTraits>;
    Stack<Monom> done;
    RStack<Monom> todo;
    todo->push(Monom { .numeral = 1, .term = TermList(t), });
    while (todo->isNonEmpty()) {
      auto next = todo->pop();

      optionIfThenElse(
          [&]() { return NumTraits::ifAdd([&](auto l, auto r) {
            todo->push(Monom { next.numeral, l });
            todo->push(Monom { next.numeral, r });
            }); },
          [&]() { return NumTraits::ifNumMul([&](auto k, auto t) {
            todo->push(Monom { next.numeral * k, t });
            }); },
          [&]() { 
            if (next.numeral != 0) {
              auto inner = AnyAlascaTerm::normalize(TypedTermList(next.term, NumTraits::sort()))
                        .template downcast<NumTraits>();
              for (auto m : inner.iterMonoms()) {
                done->push(Monom { next.numeral, m });
              }
            }
          });
    }

    /* summing up */
    if (done.size() != 0) {
      done.sort([](auto& l, auto& r) { return l.term < r.term; });
      auto sz = 0;
      auto i = 0;
      while (i < done.size()) {
        ASS_L(sz, i)
        if (done[sz].term == done[i].term) {
          done[sz].numeral += done[i].numeral;
          i++;
        } else {
          ASS(done[sz].term < done[i].term)
          if (done[sz].numeral == 0) {
            done[sz] = done[i];
            i++;
          } else {
            sz++;
            done[sz] = done[i];
            i++;
          }
        }
      }
      if (done[sz].numeral != 0) {
        sz++;
      }
      done.pop(done.size() - sz);
    }

    return AlascaTermApplNum<NumTraits>(std::move(done));
  }

} // namespace Kernel

#undef DEBUG
 
#endif // __ALASCA_Term__


