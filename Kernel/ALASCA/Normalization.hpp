/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Normalization__
#define __ALASCA_Normalization__

#include "Kernel/Term.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
// TODO remove(?)
#include "Inferences/PolynomialEvaluation.hpp"

#define DEBUG_NORM(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
namespace Kernel {

  /** 
   * Represents an inequality literal normalized for the rule FourierMotzkin.
   * this means it is a literal of the form
   *      term == 0 or term != 0 or term >= 0 or term > 0 (for Reals and Rationals)
   * or   term == 0 or term != 0              or term > 0 (for Integers)
   */
  template<class NumTraits_>
  struct __AlascaLiteralItp 
  {
    using NumTraits = NumTraits_;
    using Numeral = typename NumTraits_::ConstantType;
    AlascaTermItp<NumTraits> _term;
    AlascaPredicate _symbol;
    // TODO
    mutable Option<Literal*> _literal;

    __AlascaLiteralItp(AlascaTermItp<NumTraits> term, AlascaPredicate symbol)
      : _term(std::move(term)), _symbol(symbol) 
    { _term.integrity(); }

    friend std::ostream& operator<<(std::ostream& out, __AlascaLiteralItp const& self) 
    { return out << self._term << " " << self._symbol << " 0"; }

    auto asTuple() const { return std::tie(_symbol, _term);  }
    IMPL_COMPARISONS_FROM_TUPLE(__AlascaLiteralItp)
    IMPL_HASH_FROM_TUPLE(__AlascaLiteralItp)
  };

  using AlascaLiteralCacheData = Coproduct<Literal*
    , __AlascaLiteralItp<IntTraits>
    , __AlascaLiteralItp<RatTraits>
    , __AlascaLiteralItp<RealTraits>>;
  struct AlascaLiteralCache 
    : public AlascaLiteralCacheData {

    template<class C> 
    AlascaLiteralCache(C arg) : AlascaLiteralCacheData(std::move(arg)) {}

    template<class T, class C, class H>
    friend class Lib::Perfect;
    AlascaLiteralCache const* perfectShared() &&
    { return &*Perfect<AlascaLiteralCache, PerfectPtrComparison, DefaultHash>(std::move(*this)); }

    DEBUG_CODE(static const char* cacheId() { return "AlascaLiteralCache"; })
  private:
    void* operator new(std::size_t size) { return ::operator new(size); }
  };

  class AlascaLiteralUF {
    AlascaLiteralCache const* _self;
  public:
    explicit AlascaLiteralUF(AlascaLiteralCache const* self) : _self(self) {  }
    Literal* toLiteral() const { return _self->unwrap<Literal*>(); }
    friend std::ostream& operator<<(std::ostream& out, AlascaLiteralUF const& self)
    { return out << self._self; }
  };

  /** 
   * Represents an inequality literal normalized for the rule FourierMotzkin.
   * this means it is a literal of the form
   *      term == 0 or term != 0 or term >= 0 or term > 0 (for Reals and Rationals)
   * or   term == 0 or term != 0              or term > 0 (for Integers)
   */
  template<class NumTraits_>
  class AlascaLiteralItp 
  {
    AlascaLiteralCache const* _self;
  public:
    using NumTraits = NumTraits_;
    using Numeral = typename NumTraits_::ConstantType;
    AlascaLiteralItp(AlascaLiteralCache const* self) : _self(self) {}
  private:
    __AlascaLiteralItp<NumTraits>const& self() const { return _self->template unwrap<__AlascaLiteralItp<NumTraits>>(); }

  public:

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    AlascaTermItp<NumTraits> const& term() const
    { return self()._term; }

    AlascaPredicate symbol() const
    { return self()._symbol; }

    NumTraits numTraits() const { return NumTraits{}; }

    friend std::ostream& operator<<(std::ostream& out, AlascaLiteralItp const& self) 
    { return out << self.self(); }

    AlascaLiteralItp negation() const
    {
      auto newSym = [&](){
          switch(self()._symbol) {
            case AlascaPredicate::EQ:  return AlascaPredicate::NEQ;
            case AlascaPredicate::NEQ: return AlascaPredicate::EQ;
            case AlascaPredicate::GREATER: return AlascaPredicate::GREATER_EQ;
            case AlascaPredicate::GREATER_EQ: return AlascaPredicate::GREATER;
          }
          ASSERTION_VIOLATION
      }();
      auto newTerm = [&](){
          switch(self()._symbol) {
            case AlascaPredicate::EQ:  
            case AlascaPredicate::NEQ: return self()._term;
            case AlascaPredicate::GREATER: 
            case AlascaPredicate::GREATER_EQ: return -self()._term; 
          }
          ASSERTION_VIOLATION
      }();
      return AlascaLiteralItp(AlascaLiteralCache(__AlascaLiteralItp(newTerm, newSym)).perfectShared());
    }

    Literal* toLiteral() const
    { 
      return self()._literal.unwrapOrInit([&]() {
        auto lit = createLiteral<NumTraits>(symbol(), term().toTerm());
        lit->setAlascaTermCache(_self);
        return lit;
      });
    }

    // TODO remove
    Literal* denormalize() const
    { return toLiteral(); }

    bool isInequality() const
    { return Kernel::isInequality(symbol()); }

    // TODO perfect sharing use
    auto asTuple() const { return std::tie(self()._symbol, self()._term);  }

    IMPL_COMPARISONS_FROM_TUPLE(AlascaLiteralItp)
    IMPL_HASH_FROM_TUPLE(AlascaLiteralItp)
  };

  using AlascaLiteralItpAny = Coproduct< 
                                   AlascaLiteralItp< IntTraits>
                                 , AlascaLiteralItp< RatTraits>
                                 , AlascaLiteralItp<RealTraits>
                                 >;

  class AlascaLiteral {
    Coproduct<AlascaLiteralUF, 
      AlascaLiteralItp<IntTraits>, 
      AlascaLiteralItp<RatTraits>, 
      AlascaLiteralItp<RealTraits>> _self;


    template<class NumTraits>
    static auto cvt(__AlascaLiteralItp<NumTraits> const&, AlascaLiteralCache const* cache)
    { return AlascaLiteralItp<NumTraits>(cache); }

    static auto cvt(Literal* const&, AlascaLiteralCache const* cache)
    { return AlascaLiteralUF(cache); }


    static decltype(_self) cvt(AlascaLiteralCache const* cache)
    { return cache->applyCo([cache](auto& x) { return cvt(x, cache); }); }
  public:
    AlascaLiteral(AlascaLiteralCache const* self) : _self(cvt(self)) {}

    template<class F>
    auto apply(F f) const -> decltype(auto) { return _self.apply(f); }

    // template<class T>
    // auto as() const -> decltype(auto) { return _self.template as<T>(); }
    
    template<class NumTraits>
    static Option<AlascaLiteralItpAny> asItp(AlascaLiteralItp<NumTraits> const& n) { return some(AlascaLiteralItpAny(n)); }
    static Option<AlascaLiteralItpAny> asItp(AlascaLiteralUF             const& n) { return {}; }
    auto asItp() const -> Option<AlascaLiteralItpAny>
    { return apply([](auto& x) { return asItp(x); }); }

    Literal* toLiteral() const 
    { return apply([](auto x) { return x.toLiteral(); }); }
  };




  using AnyConstantType = Coproduct< IntegerConstantType
                                   , RationalConstantType
                                   , RealConstantType
                                   >;

  /** 
   * Represents an inequality literal normalized for the rule FourierMotzkin.
   * this means it is a literal of the form
   *      term > 0 or term >= 0 (for Reals and Rationals)
   * or   term > 0              (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    AlascaLiteralItp<NumTraits> _self;

  public:
    InequalityLiteral(AlascaTermItp<NumTraits> term, bool strict) 
      : InequalityLiteral(AlascaLiteralItp<NumTraits>(term, strict ? AlascaPredicate::GREATER : AlascaPredicate::GREATER_EQ))
    {}

    AlascaLiteralItp<NumTraits> const& inner() const { return _self; }

    explicit InequalityLiteral(AlascaLiteralItp<NumTraits> self) 
      : _self(std::move(self)) 
    { ASS(self.isInequality()) }

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    AlascaTermItp<NumTraits> const& term() const
    { return _self.term(); }

    /* 
     * returns whether this is a strict inequality (i.e. >), 
     * or a non-strict one (i.e. >=) 
     * */
    bool strict() const
    { return _self.symbol() == AlascaPredicate::GREATER; }

    friend std::ostream& operator<<(std::ostream& out, InequalityLiteral const& self) 
    { return out << self._self; }

    Literal* denormalize() const
    { return _self.denormalize(); }

  };

  using AnyInequalityLiteral = Coproduct< InequalityLiteral< IntTraits>
                                        , InequalityLiteral< RatTraits>
                                        , InequalityLiteral<RealTraits>
                                        >;

  template<class NumTraits>
  static Option<InequalityLiteral<NumTraits>> tryInequalityLiteral(AlascaLiteralItp<NumTraits> lit) 
  { return someIf(lit.isInequality(), [&](){ return InequalityLiteral(std::move(lit)); }); }
  class InequalityNormalizer 
  {
    Inferences::PolynomialEvaluation _eval;

    // TODO get rid of this global state
    static std::shared_ptr<InequalityNormalizer> globalNormalizer;

  public:
    static std::shared_ptr<InequalityNormalizer> initGlobal(InequalityNormalizer norm) {
      globalNormalizer = Lib::make_shared(std::move(norm));
      return globalNormalizer;
    }
    static std::shared_ptr<InequalityNormalizer> global() {
      ASS(globalNormalizer)
      return globalNormalizer;
    }

    // TODO remove InequalityNormalizer (?)
    AnyAlascaTerm normalize(TypedTermList term) const
    { return AnyAlascaTerm::normalize(term); }

  private:
    template<class Numeral>
    static Numeral intDivide(Numeral gcd, Numeral toCorrect)
    { 
      auto out = toCorrect / gcd; 
      ASS(out.isInt())
      return out;
    }

    static IntegerConstantType intDivide(IntegerConstantType gcd, IntegerConstantType toCorrect)
    { return toCorrect.intDivide(gcd); }

    template<class Numeral>
    static Numeral qGcd(Numeral l, Numeral r)
    { return Numeral(  l.numerator().gcd(r.numerator()),
                     l.denominator().lcm(r.denominator())); }

    static IntegerConstantType qGcd(IntegerConstantType l, IntegerConstantType r)
    { return l.gcd(r); }

    template<class NumTraits>
    static auto normalizeFactors(AlascaTermItp<NumTraits> in) -> AlascaTermItp<NumTraits>
    {
      auto gcd = in.iterSummands()
        .map([](auto s) { return s.numeral().abs(); })
        .fold([](auto l, auto r) { return qGcd(l,r); });
      if (gcd.isNone()) {
        return in;
      }
      ASS_REP(*gcd >= 0, *gcd)
      if (*gcd == 1 || *gcd == 0) {
        return in;
      } else {
        return AlascaTermItp<NumTraits>::fromCorrectlySortedIter(in.iterSummands()
            .map([=](auto s) { return AlascaMonom<NumTraits>(intDivide(*gcd, s.numeral()), s.atom()); }));
      }
    }

  public:

    template<class NumTraits> 
    Option<__AlascaLiteralItp<NumTraits>> computeNormalizedItp(Literal* lit) const
    {
      DEBUG_NORM(0, "in: ", *lit, " (", NumTraits::name(), ")")
      using ASig = AlascaSignature<NumTraits>;



      auto impl = [&]() -> Option<__AlascaLiteralItp<NumTraits>> {

        constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

        auto f = lit->functor();
        if (!theory->isInterpretedPredicate(f))
          return {};

        auto itp = theory->interpretPredicate(f);

        AlascaPredicate pred;
        TermList l, r; // <- we rewrite to l < r or l <= r
        switch(itp) {
         
          case Interpretation::EQUAL:/* l == r or l != r */
            if (SortHelper::getEqualityArgumentSort(lit) != ASig::sort()) 
              return {};
            if (ASig::isZero(*lit->nthArgument(0))) {
              l = *lit->nthArgument(0);
              r = *lit->nthArgument(1);
            } else {
              l = *lit->nthArgument(1);
              r = *lit->nthArgument(0);
            }
            pred = lit->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ;
            break;

          case NumTraits::leqI: /* l <= r */
            l = *lit->nthArgument(0);
            r = *lit->nthArgument(1);
            pred = AlascaPredicate::GREATER_EQ;
            break;

          case NumTraits::geqI: /* l >= r ==> r <= l */
            l = *lit->nthArgument(1);
            r = *lit->nthArgument(0);
            pred = AlascaPredicate::GREATER_EQ;
            break;

          case NumTraits::lessI: /* l < r */
            l = *lit->nthArgument(0);
            r = *lit->nthArgument(1);
            pred = AlascaPredicate::GREATER;
            break;

          case NumTraits::greaterI: /* l > r ==> r < l */
            l = *lit->nthArgument(1);
            r = *lit->nthArgument(0);
            pred = AlascaPredicate::GREATER;
            break;

          case NumTraits::isIntI: /* l > r ==> r < l */
            if (isInt) {
              l = NumTraits::constantTl(0);
              r = NumTraits::constantTl(0);
            } else {
              l = NumTraits::floor(*lit->nthArgument(0));
              r = *lit->nthArgument(0);
            }
            pred = lit->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ;
            break;

          default: 
            return {};
        }

        if (lit->isNegative() && isInequality(pred)) {
          // ~(l >= r) <==> (r < l)
          std::swap(l, r);
          pred = pred == AlascaPredicate::GREATER ? AlascaPredicate::GREATER_EQ : AlascaPredicate::GREATER;
        }

        if (isInt && pred == AlascaPredicate::GREATER_EQ) {
          /* l <= r ==> l < r + 1 */
          r = ASig::add(r, ASig::one());
          pred = AlascaPredicate::GREATER;
        }

        /* l < r ==> r > l ==> r - l > 0 */
        auto t = l == ASig::zero() ? r 
               : r == ASig::zero() ? ASig::minus(l)
               : ASig::add(r, ASig::minus(l));

        ASS(!isInt || pred != AlascaPredicate::GREATER_EQ)

        auto factorsNormalized = normalizeFactors(normalize(TypedTermList(t, ASig::sort())).asSum<NumTraits>().unwrap());
        switch(pred) {
          case AlascaPredicate::EQ:
          case AlascaPredicate::NEQ:
            // normalizing s == t <-> -s == -t
            if (factorsNormalized.iterSummands().hasNext()) {
              // TODO choose the numeral as the pivot if there is one
              if (factorsNormalized.iterSummands().next().numeral() < 0) {
                factorsNormalized = -factorsNormalized;
              }
            }
          case AlascaPredicate::GREATER:
          case AlascaPredicate::GREATER_EQ:
            break;
        }

        return some(__AlascaLiteralItp<NumTraits>(factorsNormalized, pred));
      };
      auto out = impl();
      DEBUG_NORM(0, "out: ", out);
      return out;
    }

    template<class NumTraits> 
    Option<AlascaLiteralItp<NumTraits>> tryNormalizeInterpreted(Literal* lit) const
    { return tryNormalizeInterpreted(lit)
        .andThen([&](auto x) { return x.template as<AlascaLiteralItp<NumTraits>>().toOwned(); }); }

    template<class NumTraits> 
    Option<AlascaLiteralItp<NumTraits>> normalize(Literal* l)
    { return tryNormalizeInterpreted<NumTraits>(l); }


    AlascaLiteralCache computeNormalized(Literal* lit) const  {
      auto itp = tryNumTraits([&](auto n) {
          return computeNormalizedItp<decltype(n)>(lit)
            .map([](auto norm) { return AlascaLiteralCache(std::move(norm)); });
      });
      if (itp) {
        return *itp;
      } else {
        /* uninterpreted */
        return AlascaLiteralCache(Literal::createFromIter(lit, 
              concatIters(
                typeArgIter(lit),
                termArgIterTyped(lit)
                .map([&](auto arg) { return normalize(arg).toTerm(); })
                )));
      }
    }


    AlascaLiteral normalize(Literal* lit) const 
    {
      auto cache = lit->getAlascaTermCache<AlascaLiteralCache>();
      if (cache == nullptr) {
        auto res = computeNormalized(lit);
        DEBUG_NORM(0, *lit, " ==> ", res)
        lit->setAlascaTermCache(std::move(res).perfectShared());
      }
      return AlascaLiteral(lit->getAlascaTermCache<AlascaLiteralCache>());

    }

    Option<AlascaLiteralItpAny> tryNormalizeInterpreted(Literal* lit) const
    { return normalize(lit).asItp().toOwned(); }

    // TODO create toTerm function for AlascaLiteralUF
    Literal* normalizedLiteral(Literal* lit) const
    { return normalize(lit).toLiteral(); }

    bool equivalent(TermList lhs, TermList rhs) 
    { 
      if (lhs.isVar() && rhs.isVar()) {
        return lhs == rhs;
      } 
      TermList sort;
      if (lhs.isTerm() && rhs.isTerm()) {
        auto s1 = SortHelper::getResultSort(lhs.term());
        auto s2 = SortHelper::getResultSort(rhs.term());

        if (s1 != s2) return false;
        else sort = s1;
      } else {
        sort = lhs.isTerm() ? SortHelper::getResultSort(lhs.term()) 
                            : SortHelper::getResultSort(rhs.term());
      }
      return equivalent(TypedTermList(lhs, sort), TypedTermList(rhs, sort));
    }

    bool equivalent(Literal* lhs, Literal* rhs) 
    { 
       auto s1 = normalizedLiteral(lhs);
       auto s2 = normalizedLiteral(rhs);
       return s1 == s2;
     }

    bool equivalent(TypedTermList lhs, TypedTermList rhs) 
    { return normalize(lhs) == normalize(rhs); }


  private: 
    Literal* normalizeUninterpreted(Literal* lit) const
    {
      RStack<TermList> args;
      args->loadFromIterator(concatIters(
            typeArgIter(lit),
            termArgIterTyped(lit)
              .map([&](auto arg) { return normalize(arg).toTerm(); })
          ));
      auto out = Literal::create(lit, args->begin());
      DEBUG_NORM(0, *lit, " ==> ", *out)
      return out;
    }
  };


} // namespace Kernel
 
#endif // __ALASCA_Normalization__

