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
#include "Lib/Perfect.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
#include "Lib/SmallArray.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/VirtualIterator.hpp"


#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
#define DEBUG_NORM_DETAILS(...) if (0) { DBG(__VA_ARGS__) }
#define INTEGRITY_CHECKS(...)  DEBUG_CODE(if (0) { __VA_ARGS__ })

#define DEBUG_RESULT(lvl, msg, ...)                                                       \
     auto impl = [&]() { __VA_ARGS__ };                                                   \
     DEBUG(lvl, msg, "???");                                                              \
     auto res = [&]() { DBG_INDENT; return impl(); }();                                   \
     DEBUG(lvl, msg, Output::ptr(res));                                                   \
     return res;                                                                          \

#define DEBUG_FN_RESULT(lvl, msg, ...)                                                    \
  { DEBUG_RESULT(lvl, msg, __VA_ARGS__) }

#define DECL_LIN_MUL_OPS(Type)                                                            \
    friend Type operator/(Type const& t, Numeral n) { return n.inverse() * t; }           \
    friend Type operator/(Type const& t, int n) { return t / Numeral(n); }                \
    friend Type operator*(int n, Type const& t) { return Numeral(n) * t; }                \
    Type operator-() const { return -1 * *this; }                                         \

namespace Kernel {
  class AlascaTermCache;

#define OPS_FROM_TO_TERM(Type)                                                            \
  auto asTuple() const { return std::tuple(toTerm()); }                                   \
  IMPL_COMPARISONS_FROM_TUPLE(Type)                                                       \
  IMPL_HASH_FROM_TUPLE(Type)                                                              \
  friend std::ostream& operator<<(std::ostream& out, Type const& self) { return out << self.toTerm(); } \

  struct __AlascaTermUF {
    TypedTermList _self;
    __AlascaTermUF(TypedTermList t) : _self(t) { }
    TypedTermList toTerm(AlascaTermCache const* cache) const { 
      if (_self.isTerm()) {
        ASS_REP(_self.term()->getAlascaTermCache<AlascaTermCache>() == cache, Output::cat(_self, " ", Output::ptr(_self.term()->getAlascaTermCache<AlascaTermCache>())))
      }
      return _self; 
    }
    static __AlascaTermUF normalizeUF(Term* t);
    using Self = __AlascaTermUF;
    auto asTuple() const { return std::make_tuple(_self); }
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    Option<TypedTermList> asVar() const  { ASS(_self.isVar()) return {}; }
  };


  template<class NumTraits>
  class AlascaMonom {
    using Numeral = typename NumTraits::ConstantType;
    using ASig = AlascaSignature<NumTraits>;
    Numeral _numeral;
    TermList _term;
  public:

    AlascaMonom(Numeral numeral, TermList term) 
      : _numeral(std::move(numeral))
      , _term(std::move(term)) 
    {  }

    void integrity() const 
    { ASS_REP(ASig::one() == _term || !ASig::isNumeral(_term), _term) }

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

    friend class AlascaTermCache;
    TypedTermList toTerm() const { 
      return TypedTermList(
            _numeral == 1 ? _term 
          : isNumeral() == 1 ? NumTraits::constantTl(_numeral) 
          : ASig::linMul(_numeral, _term)
          , NumTraits::sort()); 
    }

    using Self = AlascaMonom;
    auto asTuple() const { return std::tie(_term, _numeral); }
    IMPL_COMPARISONS_FROM_TUPLE(Self)
    IMPL_HASH_FROM_TUPLE(Self)
    friend std::ostream& operator<<(std::ostream& out, AlascaMonom const& self) 
    { return out << self._numeral << " " << self._term; }
  };


  /* T can be either TermList or TermSpec */
  template<class NumTraits>
  struct __AlascaTermItp 
  {
    mutable Option<TypedTermList> _self;
    using Numeral = typename AlascaSignature<NumTraits>::Numeral;
    SmallArray<AlascaMonom<NumTraits>, 1> _sum;

    __AlascaTermItp(decltype(_sum) sum) : _sum(std::move(sum)) {}
  public:
    __AlascaTermItp(__AlascaTermItp&&) = default;
    __AlascaTermItp& operator=(__AlascaTermItp&&) = default;
    template<class Iter>
    static __AlascaTermItp fromCorrectlySortedIter(Iter iter) 
    { return __AlascaTermItp(decltype(_sum)::fromIterator(std::move(iter))); }

    unsigned nSummands() const { return _sum.size(); }
    auto& monomAt(unsigned i) const { return _sum[i]; }
    auto iterSummands() const { return arrayIter(_sum); }
    Option<TypedTermList> asTrivial() const { 
      return someIf(nSummands() == 1 && monomAt(0).numeral() == 1, 
          [&]() { return TypedTermList(monomAt(0).atom(), NumTraits::sort()); });
    }
    Option<TypedTermList> asVar() const { 
      if (auto out = asTrivial()) {
        if (out->isVar()) {
          return out;
        }
      }
      return {};
    }

    TypedTermList toTerm(AlascaTermCache const* self) const
    { return _self.unwrapOrInit([&]() -> TypedTermList { 
      auto term = NumTraits::sum(arrayIter(_sum).map([](auto& m) { return TermList(m.toTerm()); }));
      if (term.isTerm()) {
        term.term()->setAlascaTermCache(self);
      }
      return TypedTermList(term, NumTraits::sort()); }); 
    }

    using Self = __AlascaTermItp;
    auto asTuple() const { return std::tie(_sum); }
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
  };

  struct __AlascaTermVar {
    TypedTermList _self;
    __AlascaTermVar(TypedTermList t) : _self(t) { ASS(_self.isVar()) }
    TermList sort() const { return _self.sort(); }
    static __AlascaTermVar normalize(TypedTermList t) { return __AlascaTermVar(t); }
    TypedTermList toTerm() const { return _self; }
    using Self = __AlascaTermVar;
    auto asTuple() const { return std::tie(_self); }
    IMPL_COMPARISONS_FROM_TUPLE(Self)
    IMPL_HASH_FROM_TUPLE(Self)
    friend std::ostream& operator<<(std::ostream& out, __AlascaTermVar const& self)
    { return out << self._self; }
  };


  class AlascaTermCache {
    template<class NumTraits>
    friend struct __AlascaTermItp;
    using Inner = Coproduct<__AlascaTermUF
      , __AlascaTermItp<IntTraits>
      , __AlascaTermItp<RatTraits>
      , __AlascaTermItp<RealTraits>
      >;
    Inner _self;
    template<class C>
    AlascaTermCache(C inner) : _self(std::move(inner)) {}
    template<class NumTraits>
    friend class AlascaTermItp;

    template<class T, class C, class H>
    friend class Lib::Perfect;

    void* operator new(std::size_t size) { return ::operator new(size); }
  public:
    void operator delete(void* ptr, std::size_t size) noexcept { ::operator delete(ptr); }
    Option<TypedTermList> asVar() const { return _self.apply([&](auto& x) { return x.asVar(); }); }
#if VDEBUG
    static const char* cacheId() { return "AlascaTermCache"; }
#endif // VDEBUG

    AlascaTermCache const* perfectShared() &&
    { return &*Perfect<AlascaTermCache, PerfectPtrComparison, DefaultHash>(std::move(*this)); }
    AlascaTermCache(AlascaTermCache &&) = default;
    friend struct AlascaTermImpl;

    static AlascaTermCache const* computeNormalizationUF(Term* t)
    { 
      auto ufNorm = __AlascaTermUF::normalizeUF(t);
      auto out = AlascaTermCache(ufNorm).perfectShared();
      ASS(ufNorm._self.isTerm())
      ufNorm._self.term()->setAlascaTermCache(out);
      return out;
    }

    template<class NumTraits>
    static AlascaTermCache const* computeNormalizationNum(Term* t);

    TypedTermList toTerm() const { return _self.apply([&](auto& self) { return self.toTerm(this); }); }

    using Self = AlascaTermCache;
    auto asTuple() const { return std::tie(_self); }
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self)
    { return out << self.toTerm(); }
    IMPL_HASH_FROM_TUPLE(Self);
  };

  struct AlascaTermRepr : public Coproduct<AlascaTermCache const* , __AlascaTermVar> {
    AlascaTermRepr(AlascaTermCache const* c) : Coproduct<AlascaTermCache const* , __AlascaTermVar>(std::move(c)) {}
    AlascaTermRepr(__AlascaTermVar c) : Coproduct<AlascaTermCache const* , __AlascaTermVar>(std::move(c)) {}
    auto asTuple() const {
      // This is used in order to make sure that the unit cached sum X0 is the same 
      // thing as the non-cached variable X0
      using Out = Coproduct<AlascaTermCache const* , __AlascaTermVar>;
      if (auto cache = as<AlascaTermCache const*>()) {
        if (auto var = cache.unwrap()->asVar()) {
          return Out(__AlascaTermVar(*var));
        }
      } 
      return Out(*this);
    }
    IMPL_COMPARISONS_FROM_TUPLE(AlascaTermRepr);
    IMPL_HASH_FROM_TUPLE(AlascaTermRepr);
  };

  
  /* an alasca term of numerals sort NumTraits */
  template<class NumTraits>
  class AlascaTermItp {
    using Var = __AlascaTermVar;
    using Appl = AlascaTermCache const*;
    // the internal representation is either a `Var` a variable together with a sort annotation, or an applcation term `Appl`
    // Appl terms are cached for each Term*, thus they are present as a Pointer (Appl*), while variables cannot be cached, 
    // thus they are plain owned data
    AlascaTermRepr _self;
    template<class C> AlascaTermItp(C inner) : _self(std::move(inner)) {}
    AlascaTermItp(AlascaTermCache* inner) 
      : _self(static_cast<AlascaTermCache const*>(inner)) {}
    friend struct AlascaTermImpl;
    friend class AnyAlascaTerm;
    auto& unwrapAppl() const { return _self.unwrap<AlascaTermCache const*>()->_self.template unwrap<__AlascaTermItp<NumTraits>>(); }
  public:
    static AlascaTermItp fromVar(TypedTermList v)  
    { 
      ASS_EQ(v.sort(), NumTraits::sort())
      ASS(v.isVar())
      return AlascaTermItp(__AlascaTermVar::normalize(v)); 
    }

    template<class Iter>
    static AlascaTermItp fromCorrectlySortedIter(Iter iter)
    {
      ASS(iter.knowsSize()) 
      auto create = [&]() {
        if (iter.size() == 1) {
          auto v = iter.next();
          if (v.atom().isVar() && v.numeral() == 1) {
            return fromVar(TypedTermList(v.atom(), NumTraits::sort()));
          } else {
            return AlascaTermItp(AlascaTermCache(__AlascaTermItp<NumTraits>::fromCorrectlySortedIter(iterItems(std::move(v)))).perfectShared());
          }
        } else {
          return AlascaTermItp(AlascaTermCache(__AlascaTermItp<NumTraits>::fromCorrectlySortedIter(std::move(iter))).perfectShared());
        }
      };
      auto out = create();
      INTEGRITY_CHECKS(
      out.integrity();
      )
      return out;
    }
    using Numeral = typename NumTraits::ConstantType;

    friend AlascaTermItp operator*(Numeral const& n, AlascaTermItp const& self) 
    { return AlascaTermItp::fromCorrectlySortedIter(self.iterSummands()
          .map([&](auto m) { return n * m; })); }

    DECL_LIN_MUL_OPS(AlascaTermItp)

    Option<Numeral> tryNumeral() const 
    { if (nSummands() == 0) return some(Numeral(0)); 
      else if (nSummands() == 1) return monomAt(0).tryNumeral();
      else return {}; }

    unsigned nSummands() const { return _self.match(
        [&](Appl const& x) { return unwrapAppl().nSummands(); },
        [&](Var  const& x) { return unsigned(1); }
        ); }

    auto monomAt(unsigned i) const { return _self.match(
        [&](Appl const& x) { return unwrapAppl().monomAt(i); },
        [&](Var  const& x) { return AlascaMonom<NumTraits>(1, x.toTerm()); }
        ); }

    auto operator[](unsigned i) const { return monomAt(i); }

    auto iterSummands() const { return coproductIter(_self.map(
        [&](Appl const& x) { return unwrapAppl().iterSummands().map([](auto& monom) { return monom; }); },
        [&](Var  const& x) { return iterItems(monomAt(0)); }
        )); }

    TypedTermList toTerm() const { return _self.match(
        [&](Appl const& x) { return unwrapAppl().toTerm(_self.unwrap<AlascaTermCache const*>()); },
        [&](Var  const& x) { return x.toTerm(); }
        ); }

    AlascaMonom<NumTraits> summandAt(unsigned i) const { return _self.match(
        [&](Appl const& x) { return unwrapAppl().monomAt(i); },
        [&](Var  const& x) { ASS_EQ(i, 0); return AlascaMonom<NumTraits>(1, x.toTerm()); }
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

    using Self = AlascaTermItp;
    auto asTuple() const { return std::tie(_self); }

    IMPL_COMPARISONS_FROM_TUPLE(Self)
    IMPL_HASH_FROM_TUPLE(Self)
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { return out << self.toTerm(); }
  };

  using AlascaTermItpAny  = Coproduct<
        AlascaTermItp<IntTraits>
      , AlascaTermItp<RealTraits>
      , AlascaTermItp<RatTraits>
      >;

  namespace Impl {


  };

  struct AlascaTermImpl {

    template<class NumTraits>
    static Option<AlascaTermItpAny> asSum(__AlascaTermItp<NumTraits> const&, AlascaTermCache const* self) 
    { return some(AlascaTermItpAny(AlascaTermItp<NumTraits>(self))); }

    static Option<AlascaTermItpAny> asSum(__AlascaTermUF const& t, AlascaTermCache const* self) 
    { 
      forEachNumTraits([&](auto n) { ASS_REP(t.toTerm(self).sort() != n.sort(), t.toTerm(self)) });
      return {};
    }

    static Option<AlascaTermItpAny> asSum(AlascaTermCache const* const& t) 
    { return t->_self.apply([&](auto& x) { return asSum(x, t); }); }

    static Option<AlascaTermItpAny> asSum(__AlascaTermVar const& t) 
    { 
      return tryNumTraits([&](auto n){
          return someIf(n.sort() == t.sort(), 
              [&]() { return AlascaTermItpAny(AlascaTermItp<decltype(n)>::fromVar(t.toTerm())); });
      });
    }
  };

  /* we split AnyAlascaTerm into first representation definition, and then 
   * function implementation in order to be able to define a BottomUpChildIter
   * on it before defining its methods, as iterSubterms returns a struct that contains 
   * the BottomUpChildIter */ 
  struct AnyAlascaTermStruct 
  { 
    AlascaTermRepr _self;

    template<class C>
    AnyAlascaTermStruct(C inner) : _self(std::move(inner)) {}
  };
} // namespace Kernel
namespace Lib {
  template<>
  struct BottomUpChildIter<AnyAlascaTermStruct> {
    using Context = std::tuple<>;
    using Inner = Coproduct<TypedTermList
          , AlascaTermItp< IntTraits>
          , AlascaTermItp< RatTraits>
          , AlascaTermItp<RealTraits>
          >;

    Inner _self;
    unsigned _idx;

    BottomUpChildIter(AnyAlascaTermStruct t, Context);

    static unsigned nChildren(TypedTermList const& self) { return self.isVar() ? 0 : self.term()->arity();  }
    template<class NumTraits>
    static unsigned nChildren(AlascaTermItp<NumTraits> const& self) { return self.nSummands(); }

    unsigned nChildren(Context = {}) const { return _self.apply([](auto& x) { return nChildren(x); }); }

    static TypedTermList childAt(unsigned i, TypedTermList const& self)
    { return TypedTermList(*self.term()->nthArgument(0), SortHelper::getArgSort(self.term(), i)); }
    template<class NumTraits>
    static TypedTermList childAt(unsigned i, AlascaTermItp<NumTraits> const& self)
    { return TypedTermList(self.monomAt(i).atom(), NumTraits::sort()); }

    AnyAlascaTermStruct childAt(unsigned i, Context = {}) const; // { return _self.apply([&](auto& x) { return AnyAlascaTerm::normalize(childAt(i, x)); }); }

    AnyAlascaTermStruct self(Context = {}) const { return _self.apply([](auto& x) { return self(x); }); }

    static AnyAlascaTermStruct self(TypedTermList const& self);
    template<class NumTraits>
    static AnyAlascaTermStruct self(AlascaTermItp<NumTraits> const& self);

    bool hasNext(Context = {}) const { return _idx < nChildren(); }
    AnyAlascaTermStruct next(Context = {}) { return childAt(_idx++); }
  };
} // namespace Lib
namespace Kernel {

  class AnyAlascaTerm 
  { 
    AnyAlascaTermStruct _self;
    friend struct Lib::BottomUpChildIter<AnyAlascaTermStruct>;

    template<class C>
    AnyAlascaTerm(C inner) : _self(std::move(inner)) {}
    static AlascaTermCache const* computeNormalization(Term* t, TermList sort);
  public:

    static AnyAlascaTerm normalize(TypedTermList t);

    template<class NumTraits>
    static AnyAlascaTerm from(AlascaTermItp<NumTraits> t) 
    { return AnyAlascaTerm(t._self); }

    TypedTermList toTerm() const
    { return _self._self.match([&](auto& ptr  ) { return ptr->toTerm(); }
                        ,[&](auto& owned) { return owned.toTerm(); }); }
    
    Option<AlascaTermItpAny> asSum() const 
    { return _self._self.apply([](auto& x) { return AlascaTermImpl::asSum(x); }); }
    
    auto iterSubterms() const
    { return iterTraits(GenericSubtermIter(this->_self, /* bottomUp */ false))
                 .map([](auto t) { return AnyAlascaTerm(t); }); }

    template<class NumTraits> Option<AlascaTermItp<NumTraits>> asSum() const 
    { return asSum().andThen([](auto x) {
          return x.template as<AlascaTermItp<NumTraits>>().toOwned(); }); }

    OPS_FROM_TO_TERM(AnyAlascaTerm);
  };

} // namespace Kernel

namespace Kernel {

  // inline IterTraits<VirtualIterator<AnyAlascaTerm>> AnyAlascaTerm::iterSubterms() const {
  //   return iterTraits(pvi(GenericSubtermIter(*this, /* bottomUp */ false)));
  // }


  inline __AlascaTermUF __AlascaTermUF::normalizeUF(Term* t) {
    return __AlascaTermUF(TypedTermList(Term::createFromIter(t->functor(), concatIters(
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
      auto out = t0.isSome() && t1.isSome() 
           ? some(TermList(Term::create(f, { *t0, *t1 })))
           : t0.isSome() ? t0
           : t1.isSome() ? t1
           : Option<TermList>();
      return out;
    } else {
      auto norm = AnyAlascaTerm::normalize(TypedTermList(TermList(t), NumTraits::sort()))
        .asSum<NumTraits>()
        .unwrap();
      if (norm.nSummands() == 0) {
        n = NumTraits::constant(0);
        return {};
      } else if (norm.nSummands() >= 2) {
        return Option<TermList>(norm.toTerm());
      } else if (auto num = norm.tryNumeral()) {
        n *= *num;
        return {};
      } else {
        ASS_EQ(norm.nSummands(), 1)
        auto m = norm.summandAt(0);
        n *= m.numeral();
        return some(m.atom());
      }
    }
  }


  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, TermList t, unsigned f)
  { return t.isVar() ? some(t) : __normalizeMul<NumTraits>(n, t.term(), f); }


  template<class NumTraits>
  Option<TermList> __normalizeMul(typename NumTraits::ConstantType& n, Term * orig_) {
    return __normalizeMul<NumTraits>(n, orig_, orig_->functor());
  }

  template<class PushTodo, class PushDone>
  bool normalizeFractionalInterpretation(IntTraits, Interpretation itp, Term* t, 
    PushTodo todo, 
    PushDone done) { return false; }


  template<class NumTraits, class PushTodo, class PushDone>
  bool normalizeFractionalInterpretation(NumTraits, Interpretation itp, Term* t, 
    PushTodo pushTodo, 
    PushDone pushDone) {

    using Numeral = typename NumTraits::ConstantType;
    switch (itp) {
      case NumTraits::divI: {
        auto rec = [](auto t) { return AnyAlascaTerm::normalize(TypedTermList(TermList(t), NumTraits::sort())); };
        auto t1 = rec(t->termArg(1));
        if (auto r = t1.template asSum<NumTraits>()->tryNumeral()) {
          if (*r != 0) {
            pushTodo(1 / *r, t->termArg(0));
            return true;
          }
        }
        pushDone(Numeral(1), NumTraits::div(
              rec(t->termArg(0)).toTerm(),
              t1.toTerm()));
        return true;
      }
      default:
        return false;
    }
  }

  template<class NumTraits>
  AlascaTermCache const* AlascaTermCache::computeNormalizationNum(Term* orig_) {
    auto orig = TermList(orig_);

    using Monom = AlascaMonom<NumTraits>;
    Stack<Monom> done;
    RStack<Monom> todo;
    todo->push(Monom(1, orig));

    auto uninterpretedCase = [&](Monom cur) {
        DEBUG_NORM_DETAILS("uninterpreted")
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
      DEBUG_NORM_DETAILS("todo: ", todo, " done: ", done)
      auto cur = todo->pop();
      if (cur.atom().isVar()) {
        if (cur.numeral() != 0) {
          done.push(cur);
        }
      } else {
        Term* t = cur.atom().term();
        if (auto k = NumTraits::tryLinMul(t->functor())) {
          DEBUG_NORM_DETAILS("linMul")
          todo->push(Monom(cur.numeral() * *k, t->termArg(0)));
        } else if (auto k = NumTraits::tryNumeral(t->functor())) {
          DEBUG_NORM_DETAILS("num")
          if (cur.numeral() != 0) {
            done.push(Monom(cur.numeral() * *k));
          }
        } else if (auto itp = theory->tryInterpretFunction(t->functor())) {
          switch(*itp) {
            case NumTraits::addI:
              DEBUG_NORM_DETAILS("add")
              todo->push(Monom(cur.numeral(), t->termArg(0)));
              todo->push(Monom(cur.numeral(), t->termArg(1)));
              break;
            case NumTraits::binMinusI:
              DEBUG_NORM_DETAILS("minus")
              todo->push(Monom( cur.numeral(), t->termArg(0)));
              todo->push(Monom(-cur.numeral(), t->termArg(1)));
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
            case NumTraits::floorI: {
              DEBUG_NORM_DETAILS("floor")
              auto norm = AnyAlascaTerm::normalize(TypedTermList(t->termArg(0), NumTraits::sort()))
                .asSum<NumTraits>()
                .unwrap();
              RStack<Monom> inner;
              for (auto m : norm.iterSummands()) {
                auto atomInt = m.isNumeral() || NumTraits::isFloor(m.atom());
                if (atomInt) {
                  auto kF = m.numeral().floor();
                  auto kR = m.numeral() - kF;
                  if (kF != 0) {
                    done.push(Monom(kF * cur.numeral(), m.atom()));
                  }
                  if (kR != 0) {
                    inner->push(Monom(kR, m.atom()));
                  }
                } else {
                  inner->push(m);
                }
              }
              if (inner.size() == 0) {

              } else if (inner.size() == 1 && inner[0].isNumeral()) {
                ASS_EQ(inner[0].tryNumeral()->floor(), 0)
              } else {
                done.push(Monom(cur.numeral(), NumTraits::floor(NumTraits::sum(
                          arrayIter(*inner)
                          .map([](auto& m) { return m.toTerm(); })
                          ))));
              }
            }
              break;
            case NumTraits::minusI:
              DEBUG_NORM_DETAILS("minus")
              todo->push(Monom(-cur.numeral(), t->termArg(0)));
              break;
            default:
              if (!normalizeFractionalInterpretation(NumTraits{}, *itp, t, 
                    [&](auto n, auto t) { todo->push(Monom(n * cur.numeral(), t)); },
                    [&](auto n, auto t) { done.push(Monom(n * cur.numeral(), t)); }
                   )) {
                uninterpretedCase(std::move(cur));
              } 
              break;
          }
        } else {
          uninterpretedCase(std::move(cur));
        }
      }
    }
    DEBUG_NORM_DETAILS("done: ", done)
    INTEGRITY_CHECKS(
      for (auto m : done) {
        m.integrity();
      }
    )

    /* summing up */
    if (done.size() != 0) {
      done.sort([](auto& l, auto& r) { return l.atom() < r.atom(); });
      unsigned sz = 0;
      unsigned i = 0;
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
    return AlascaTermCache(__AlascaTermItp<NumTraits>::fromCorrectlySortedIter(arrayIter(done))).perfectShared();
  }

  inline AlascaTermCache const* AnyAlascaTerm::computeNormalization(Term* term, TermList sort) 
  DEBUG_FN_RESULT(1, Output::cat("computeNormalization(", *term, ": ", sort, ") = "), 
  {
    return forAnyNumTraits([&](auto n) -> Option<AlascaTermCache const*> {
          if (n.sort() != sort) return {};
          return some(AlascaTermCache::computeNormalizationNum<decltype(n)>(term));
      })
      .unwrapOrElse([&]() { return AlascaTermCache::computeNormalizationUF(term); });
  }
  )


  inline AnyAlascaTerm AnyAlascaTerm::normalize(TypedTermList t) 
  {
    if (t.isVar()) {
      return AnyAlascaTerm(__AlascaTermVar::normalize(t));
    } else {
      if (t.term()->getAlascaTermCache<AlascaTermCache>() == nullptr) {
        t.term()->setAlascaTermCache(computeNormalization(t.term(), t.sort()));
      }
      return AnyAlascaTerm(t.term()->getAlascaTermCache<AlascaTermCache>());
    }
  }

} // namespace Kernel

namespace Lib {

  inline BottomUpChildIter<AnyAlascaTermStruct>::BottomUpChildIter(AnyAlascaTermStruct t, Context)
    : _self(AnyAlascaTerm(t).asSum()
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
        .orElse([&]() { return Inner(AnyAlascaTerm(t).toTerm()); }))
    , _idx(0)
  { }

  inline AnyAlascaTermStruct BottomUpChildIter<AnyAlascaTermStruct>::childAt(unsigned i, Context) const
  { return _self.apply([&](auto& x) { return AnyAlascaTerm::normalize(childAt(i, x)); })._self; }

  inline  AnyAlascaTermStruct BottomUpChildIter<AnyAlascaTermStruct>::self(TypedTermList const& self) { return AnyAlascaTerm::normalize(self)._self; }
  template<class NumTraits>
  AnyAlascaTermStruct BottomUpChildIter<AnyAlascaTermStruct>::self(AlascaTermItp<NumTraits> const& self) { return AnyAlascaTerm::from(self)._self; };


}

#undef DEBUG_FN_RESULT
#undef DEBUG_NORM
#undef DEBUG_RESULT
#undef DEBUG
#undef DECL_LIN_MUL_OPS
 
#endif // __ALASCA_Term__


