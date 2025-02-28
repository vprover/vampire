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

#include "Debug/Assertion.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/VirtualIterator.hpp"


#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
#define DEBUG_NORM(...) if (0) { DBG(__VA_ARGS__) }

#define DEBUG_RESULT(lvl, msg, ...)                                                       \
     auto impl = [&]() { __VA_ARGS__ };                                                   \
     auto res = impl();                                                                   \
     DEBUG(lvl, msg, res);                                                      \
     return res;                                                                          \

#define DEBUG_FN_RESULT(lvl, msg, ...)                                                    \
  { DEBUG_RESULT(lvl, msg, __VA_ARGS__) }

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
    {  }

    void integrity() const 
    { ASS(ASig::one() == _term || !ASig::isNumeral(_term)) }

    AlascaMonom(Numeral numeral) 
      : AlascaMonom(numeral, NumTraits::one()) 
    {  }

    bool isNumeral() const { return tryNumeral().isSome(); }
    Option<Numeral> tryNumeral() const 
    { return someIf(ASig::one() == _term, [&]() { return _numeral; }); }

    AlascaMonom(int numeral, TermList term) : AlascaMonom(Numeral(numeral), term) {}

    friend AlascaMonom operator*(Numeral const& n, AlascaMonom const& self) { return AlascaMonom(self.numeral() * n, self.atom()); }
    DECL_LIN_MUL_OPS(AlascaMonom)

    Numeral const& numeral() const { return _numeral; }
    TermList atom() const { return _term; }

    template<class N>
    friend class __AlascaTermApplNum;
    TypedTermList toTerm() const { 
      return TypedTermList(
            _numeral == 1 ? _term 
          : isNumeral() == 1 ? NumTraits::constantTl(_numeral) 
          : ASig::linMul(_numeral, _term)
          , NumTraits::sort()); 
    }

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
    template<class C>
    AlascaTermCache(C inner) : _self(std::move(inner)) {}
    template<class NumTraits>
    friend class AlascaTermNum;
  public:
    friend struct AlascaTermImpl;

    static AlascaTermCache normalizeUF(Term* t)
    { return AlascaTermCache(Inner(__AlascaTermApplUF::normalize(t))); }

    template<class NumTraits>
    static AlascaTermCache normalizeNum(Term* t);

    TypedTermList toTerm() const { return _self.apply([](auto& self) { return self.toTerm(); }); }
    OPS_FROM_TO_TERM(AlascaTermCache);
  };

  
  /* an alasca term of numerals sort NumTraits */
  template<class NumTraits>
  class AlascaTermNum {
    using Var = __AlascaTermVar;
    using Appl = AlascaTermCache;
    // the internal representation is either a `Var` a variable together with a sort annotation, or an applcation term `Appl`
    // Appl terms are cached for each Term*, thus they are present as a Pointer (Appl*), while variables cannot be cached, 
    // thus they are plain owned data
    using Inner = Coproduct<AlascaTermCache*, Var>;
    Inner _self;
    template<class C> AlascaTermNum(C inner) : _self(std::move(inner)) {}
    friend struct AlascaTermImpl;
    friend class AnyAlascaTerm;
    auto& unwrapAppl() const { return _self.unwrap<AlascaTermCache*>()->_self.template unwrap<__AlascaTermApplNum<NumTraits>>(); }
  public:
    static AlascaTermNum fromVar(TypedTermList v)  
    { 
      ASS_EQ(v.sort(), NumTraits::sort())
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
            // TODO should we set the term cache here?
            return AlascaTermNum(new AlascaTermCache(__AlascaTermApplNum<NumTraits>::fromCorrectlySortedIter(iterItems(std::move(v)))));
          }
        } else {
          return AlascaTermNum(new AlascaTermCache(__AlascaTermApplNum<NumTraits>::fromCorrectlySortedIter(std::move(iter))));
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
        [&](Appl* const& x) { return unwrapAppl().nSummands(); },
        [&](Var   const& x) { return unsigned(1); }
        ); }

    auto monomAt(unsigned i) const { return _self.match(
        [&](Appl* const& x) { return unwrapAppl().monomAt(i); },
        [&](Var   const& x) { return AlascaMonom<NumTraits>(1, x.toTerm()); }
        ); }

    auto iterSummands() const { return coproductIter(_self.map(
        [&](Appl* const& x) { return unwrapAppl().iterSummands().map([](auto& monom) { return monom; }); },
        [&](Var   const& x) { return iterItems(monomAt(0)); }
        )); }

    TypedTermList toTerm() const { return _self.match(
        [&](Appl* const& x) { return unwrapAppl().toTerm(); },
        [&](Var   const& x) { return x.toTerm(); }
        ); }

    AlascaMonom<NumTraits> summandAt(unsigned i) const { return _self.match(
        [&](Appl* const& x) { return unwrapAppl().monomAt(i); },
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
        x.integrity();

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
    static Option<AlascaTermNumAny> asSum(__AlascaTermApplNum<NumTraits> const&, AlascaTermCache* self) 
    { return some(AlascaTermNumAny(AlascaTermNum<NumTraits>(self))); }

    static Option<AlascaTermNumAny> asSum(__AlascaTermApplUF const& t, AlascaTermCache* self) 
    { 
      forEachNumTraits([&](auto n) { ASS_NEQ(t.toTerm().sort(), n.sort()) });
      return {};
    }

    static Option<AlascaTermNumAny> asSum(AlascaTermCache* const& t) 
    { return t->_self.apply([&](auto& x) { return asSum(x, t); }); }

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
    using Inner = Coproduct< AlascaTermCache*
                           , __AlascaTermVar>;
    Inner _self;

    AnyAlascaTerm(Inner inner) : _self(std::move(inner)) {}
  public:

    static AnyAlascaTerm normalize(TypedTermList t);
    template<class NumTraits>
    static AnyAlascaTerm from(AlascaTermNum<NumTraits> t) 
    { return AnyAlascaTerm(t._self); }

    TypedTermList toTerm() const
    { return _self.match([&](auto& ptr  ) { return ptr->toTerm(); }
                        ,[&](auto& owned) { return owned.toTerm(); }); }
    
    Option<AlascaTermNumAny> asSum() const 
    { return _self.apply([](auto& x) { return AlascaTermImpl::asSum(x); }); }
    
    // TODO get rid of virtual iterator here
    IterTraits<VirtualIterator<AnyAlascaTerm>> iterSubterms() const;    

    template<class NumTraits> Option<AlascaTermNum<NumTraits>> asSum() const 
    { return asSum().andThen([](auto x) {
          return x.template as<AlascaTermNum<NumTraits>>().toOwned(); }); }

    OPS_FROM_TO_TERM(AnyAlascaTerm);
  };
} // namespace Kernel

namespace Lib {
  template<>
  struct BottomUpChildIter<AnyAlascaTerm> {
    using Context = std::tuple<>;
    using Inner = Coproduct<TypedTermList
          , AlascaTermNum< IntTraits>
          , AlascaTermNum< RatTraits>
          , AlascaTermNum<RealTraits>
          >;

    Inner _self;
    unsigned _idx;

    BottomUpChildIter(AnyAlascaTerm t, Context) 
      : _self(t.asSum()
          .andThen([&](auto s) { 
            return s.apply([](auto s) -> Option<Inner> {
                if (s.nSummands() == 1 && s.monomAt(0).numeral() == 1) {
                  /* no trivial sums */
                  return {};
                } else {
                  return some(Inner(s));
                }
            });
          })
          .orElse([&]() { return Inner(t.toTerm()); })) 
      , _idx(0)
    { }

    // TODO iter type args ?

    static unsigned nChildren(TypedTermList const& self) { return self.isVar() ? 0 : self.term()->arity();  }
    template<class NumTraits>
    static unsigned nChildren(AlascaTermNum<NumTraits> const& self) { return self.nSummands(); }

    unsigned nChildren(Context = {}) const { return _self.apply([](auto& x) { return nChildren(x); }); }

    static TypedTermList childAt(unsigned i, TypedTermList const& self)
    { return TypedTermList(*self.term()->nthArgument(0), SortHelper::getArgSort(self.term(), i)); }
    template<class NumTraits>
    static TypedTermList childAt(unsigned i, AlascaTermNum<NumTraits> const& self)
    { return TypedTermList(self.monomAt(i).atom(), NumTraits::sort()); }

    auto childAt(unsigned i, Context = {}) const { return _self.apply([&](auto& x) { return AnyAlascaTerm::normalize(childAt(i, x)); }); }

    auto self(Context = {}) const { return _self.apply([](auto& x) { return self(x); }); }

    static AnyAlascaTerm self(TypedTermList const& self) { return AnyAlascaTerm::normalize(self); }
      // TODO more efficient?
    template<class NumTraits>
    static AnyAlascaTerm self(AlascaTermNum<NumTraits> const& self) { return AnyAlascaTerm::from(self); };

    bool hasNext(Context = {}) const { return _idx < nChildren(); }
    AnyAlascaTerm next(Context = {}) { return childAt(_idx++); }
  };
} // namespace Lib

namespace Kernel {

  inline IterTraits<VirtualIterator<AnyAlascaTerm>> AnyAlascaTerm::iterSubterms() const {
    return iterTraits(pvi(GenericSubtermIter(*this, /* bottomUp */ false)));
  }


  inline __AlascaTermApplUF __AlascaTermApplUF::normalize(Term* t) {
    return __AlascaTermApplUF(TypedTermList(Term::createFromIter(t->functor(), concatIters(
          typeArgIter(t),
          termArgIterTyped(t)
            .map([](auto t) { return AnyAlascaTerm::normalize(t).toTerm(); })))));
  }

  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, TermList t, unsigned f);

  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, Term * t, unsigned f) {
    if (t->functor() == f) {
      auto t0 = __normalizeMul<NumTraits>(n, t->termArg(0), f);
      auto t1 = __normalizeMul<NumTraits>(n, t->termArg(1), f);
      return t0.isSome() && t1.isSome() ?  some(TermList(Term::create(f, { *t0, *t1 })))
           : t0.isSome() ? t0
           : t1.isSome() ? t1
           : Option<TermList>();
    } else if (auto k = NumTraits::tryNumeral(t)) {
      n *= *k;
      return Option<TermList>();
    } else if  (auto k = NumTraits::tryLinMul(t)) {
      n *= *k;
      return __normalizeMul<NumTraits>(n, t->termArg(0), f);
    } else if  (NumTraits::isMinus(t)) {
      n = -n;
      return __normalizeMul<NumTraits>(n, t->termArg(0), f);
    } else {
      return some(TermList(AnyAlascaTerm::normalize(TypedTermList(TermList(t), NumTraits::sort())).toTerm()));
    }
  }


  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, TermList t, unsigned f)
  { return t.isVar() ? some(t) : __normalizeMul<NumTraits>(n, t.term(), f); }


  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, Term * orig_) {
    return __normalizeMul<NumTraits>(n, orig_, orig_->functor());
  }

  template<class NumTraits>
  __AlascaTermApplNum<NumTraits> __AlascaTermApplNum<NumTraits>::normalize(Term* orig_) {
    auto orig = TermList(orig_);

    using Monom = AlascaMonom<NumTraits>;
    Stack<Monom> done;
    RStack<Monom> todo;
    todo->push(Monom(1, orig));

    auto uninterpretedCase = [&](Monom cur) {
        DEBUG_NORM("uninterpreted")
        if (cur.numeral() != 0) {
          // TOOD we do the smae thing here as in UF::normalize
          done.push(Monom(cur.numeral(),
                  TermList(Term::createFromIter(cur.atom().term()->functor(), concatIters(
                            typeArgIter(cur.atom().term()),
                            termArgIterTyped(cur.atom().term())
                              .map([](auto t) { return AnyAlascaTerm::normalize(t).toTerm(); })))
                 )));
        }
    };
    while (todo->isNonEmpty()) {
      DEBUG_NORM("todo: ", todo, " done: ", done)
      auto cur = todo->pop();
      if (cur.atom().isVar()) {
        if (cur.numeral() != 0) {
          done.push(cur);
        }
      } else {
        Term* t = cur.atom().term();
        if (auto k = NumTraits::tryLinMul(t->functor())) {
          DEBUG_NORM("linMul")
          todo->push(Monom(cur.numeral() * *k, t->termArg(0)));
        } else if (auto k = NumTraits::tryNumeral(t->functor())) {
          DEBUG_NORM("num")
          if (cur.numeral() != 0) {
            done.push(Monom(cur.numeral() * *k));
          }
        } else if (auto itp = theory->tryInterpretFunction(t->functor())) {
          switch(*itp) {
            case NumTraits::addI:
              DEBUG_NORM("add")
              todo->push(Monom(cur.numeral(), t->termArg(0)));
              todo->push(Monom(cur.numeral(), t->termArg(1)));
              break;
            case NumTraits::mulI: {
              /* pulling out all linear parts of the multiplication
               * (x * 2 * (a * 3)) ==> 6 (x * a) */

              auto n = cur.numeral();
              auto normT = __normalizeMul<NumTraits>(n, t);
              if (normT.isSome() && NumTraits::isAdd(*normT)) {
                todo->push(Monom(n, normT->term()->termArg(0)));
                todo->push(Monom(n, normT->term()->termArg(1)));
              } else if (normT) {
                done.push(Monom(n, *normT));
              } else {
                done.push(Monom(n));
              }
            }
              break;
            //  case NumTraits::mulI: {
            //   /* pulling out all linear parts of the multiplication
            //    * (x * 2 * (a * 3)) ==> 6 * (x * a) */
            //   RStack<TermList> mulArgs;
            //   mulArgs->push(t->termArg(0));
            //   mulArgs->push(t->termArg(1));
            //   auto n = Numeral(1);
            //   RStack<TermList> mulRes;
            //   while (mulArgs->isNonEmpty()) {
            //     auto a = mulArgs->pop();
            //     if (a.isTerm() && a.term()->functor() == t->functor()) {
            //       mulArgs->push(t->termArg(0));
            //       mulArgs->push(t->termArg(1));
            //     } else {
            //       auto r = AnyAlascaTerm::normalize(TypedTermList(a, NumTraits::sort())).toTerm();
            //       if (auto k = NumTraits::tryNumeral(r)) {
            //         n *= *k;
            //       } else if (auto k = NumTraits::tryLinMul(r)) {
            //         n *= *k;
            //         mulRes->push(r.term()->termArg(0));
            //       } else {
            //         mulRes->push(r);
            //       }
            //     }
            //   }
            //   todo->push(Monom(cur.numeral() * n, NumTraits::product(arrayIter(*mulRes))));
            // }
            //   break;
            case NumTraits::floorI:
              DEBUG_NORM("floor")
              ASSERTION_VIOLATION
              break;
            case NumTraits::minusI:
              DEBUG_NORM("minus")
              todo->push(Monom(-cur.numeral(), t->termArg(0)));
              break;
            default:
              uninterpretedCase(std::move(cur));
              break;
          }
        } else {
          uninterpretedCase(std::move(cur));
        }
      }
    }
    DEBUG_NORM("done: ", done)

    /* summing up */
    if (done.size() != 0) {
      done.sort([](auto& l, auto& r) { return l.atom() < r.atom(); });
      auto sz = 0;
      auto i = 0;
      while (i < done.size()) {
        if (i == sz) {
          i++;
        } else if (done[sz].atom() == done[i].atom()) {
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

  template<class NumTraits>
  AlascaTermCache AlascaTermCache::normalizeNum(Term* t) 
  { return AlascaTermCache(Inner(__AlascaTermApplNum<NumTraits>::normalize(t))); }


  inline AnyAlascaTerm AnyAlascaTerm::normalize(TypedTermList t) 
  DEBUG_FN_RESULT(1, Output::cat("normalize(", t, ") = "), 
  {
    DBG_INDENT
    if (t.isVar()) {
      return AnyAlascaTerm(Inner(__AlascaTermVar::normalize(t)));
    } else {
      if (t.term()->getAlascaTermCache() == nullptr) {
        auto term = t.term();
        auto computeNormalization = [&]() {
          auto sort = t.sort();
          return forAnyNumTraits([&](auto n) -> Option<AlascaTermCache> {
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
  )


} // namespace Kernel

#undef DEBUG_FN_RESULT
#undef DEBUG_NORM
#undef DEBUG_RESULT
#undef DEBUG
#undef DECL_LIN_MUL_OPS
 
#endif // __ALASCA_Term__


