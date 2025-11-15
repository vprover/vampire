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
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/Polynomial.hpp"
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
  class AlascaLiteral {
  public:
    using NumTraits = NumTraits_;
    using Numeral = typename NumTraits_::ConstantType;
  private:
    Perfect<Polynom<NumTraits>> _term;
    AlascaPredicate _symbol;
    // friend struct std::hash<AlascaLiteral>;

  public:

    AlascaLiteral(Perfect<Polynom<NumTraits>> term, AlascaPredicate symbol)
      : _term(term), _symbol(symbol)
    { _term->integrity(); }

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return *_term; }

    AlascaPredicate symbol() const
    { return _symbol; }

    friend std::ostream& operator<<(std::ostream& out, AlascaLiteral const& self)
    { return out << self._term << " " << self._symbol << " 0"; }

    AlascaLiteral negation() const
    {
      auto newSym = [&](){
          switch(_symbol) {
            case AlascaPredicate::EQ:  return AlascaPredicate::NEQ;
            case AlascaPredicate::NEQ: return AlascaPredicate::EQ;
            case AlascaPredicate::GREATER: return AlascaPredicate::GREATER_EQ;
            case AlascaPredicate::GREATER_EQ: return AlascaPredicate::GREATER;
          }
          ASSERTION_VIOLATION
      }();
      auto newTerm = [&](){
          switch(_symbol) {
            case AlascaPredicate::EQ:
            case AlascaPredicate::NEQ: return _term;
            case AlascaPredicate::GREATER:
            case AlascaPredicate::GREATER_EQ: return -_term; // perfect(-(*_term))
          }
          ASSERTION_VIOLATION
      }();
      return AlascaLiteral(newTerm, newSym);
    }

    Literal* denormalize() const
    { return createLiteral<NumTraits>(symbol(), term().denormalize()) ; }

    bool isInequality() const
    { return Kernel::isInequality(symbol()); }

    bool isIsInt() const
    { return Kernel::isIsInt(symbol()); }

    auto asTuple() const { return std::tie(_symbol, _term);  }

    IMPL_COMPARISONS_FROM_TUPLE(AlascaLiteral)
    IMPL_HASH_FROM_TUPLE(AlascaLiteral)
  };


  using AnyConstantType = Coproduct< IntegerConstantType
                                   , RationalConstantType
                                   , RealConstantType
                                   >;

  using AnyAlascaLiteral = Coproduct< AlascaLiteral< IntTraits>
                                 , AlascaLiteral< RatTraits>
                                 , AlascaLiteral<RealTraits>
                                 >;

  /**
   * Represents an inequality literal normalized for the rule FourierMotzkin.
   * this means it is a literal of the form
   *      term > 0 or term >= 0 (for Reals and Rationals)
   * or   term > 0              (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    AlascaLiteral<NumTraits> _self;

  public:
    InequalityLiteral(Perfect<Polynom<NumTraits>> term, bool strict)
      : InequalityLiteral(AlascaLiteral<NumTraits>(term, strict ? AlascaPredicate::GREATER : AlascaPredicate::GREATER_EQ))
    {}

    AlascaLiteral<NumTraits> const& inner() const { return _self; }

    explicit InequalityLiteral(AlascaLiteral<NumTraits> self)
      : _self(std::move(self))
    { ASS(self.isInequality()) }

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
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
  static Option<InequalityLiteral<NumTraits>> tryInequalityLiteral(AlascaLiteral<NumTraits> lit)
  { return someIf(lit.isInequality(), [&](){ return InequalityLiteral(std::move(lit)); }); }

  class InequalityNormalizer
  {
    Inferences::PolynomialEvaluation _eval;

  public:
    static std::shared_ptr<InequalityNormalizer> global() {
      // TODO get rid of this global state
      static std::shared_ptr<InequalityNormalizer> globalNormalizer = Lib::make_shared(InequalityNormalizer());

      return globalNormalizer;
    }

    PolyNf normalize(TypedTermList term) const
    {
      TIME_TRACE("alasca normalize term")
      auto norm = PolyNf::normalize(term);
      auto out = _eval.evaluate(norm);
      return out || norm;
    }

    PolyNf normalize(TermList t) const
    { return t.isTerm() ? normalize(t.term())
                        : PolyNf(Variable(t.var())); }

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
    static auto normalizeFactors(Perfect<Polynom<NumTraits>> in) -> Perfect<Polynom<NumTraits>>
    {
      if (in->nSummands() == 0) {
        return in;
      }
      auto gcd = in->iterSummands()
        .map([](auto s) { return s.numeral.abs(); })
        .fold([](auto l, auto r) { return qGcd(l,r); })
        .unwrap();
      ASS_REP(gcd >= 0, gcd)
      if (gcd == 1 || gcd == 0) {
        return in;
      } else {
        auto  out = perfect(Polynom<NumTraits>(in->iterSummands()
              .map([=](auto s) { return Monom<NumTraits>(intDivide(gcd, s.numeral), s.factors); })
              .template collect<Stack>()));
        return out;
      }
    }

  public:

    template<class NumTraits>
    Option<AlascaLiteral<NumTraits>> tryNormalizeInterpreted(Literal* lit) const
    {
      DEBUG_NORM(0, "in: ", *lit, " (", NumTraits::name(), ")")
      using ASig = AlascaSignature<NumTraits>;

      auto impl = [&]() -> Option<AlascaLiteral<NumTraits>> {

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

        auto factorsNormalized = normalizeFactors(normalize(TypedTermList(t, ASig::sort())).wrapPoly<NumTraits>());
        switch(pred) {
          case AlascaPredicate::EQ:
          case AlascaPredicate::NEQ:
            // normalizing s == t <-> -s == -t
            if (factorsNormalized->nSummands() > 0) {
              // TODO choose the numeral as the pivot if there is one
              if (factorsNormalized->summandAt(0).numeral < 0) {
                factorsNormalized = perfect(-*factorsNormalized);
              }
            }
          case AlascaPredicate::GREATER:
          case AlascaPredicate::GREATER_EQ:
            break;
        }

        return some(AlascaLiteral<NumTraits>(factorsNormalized, pred));
      };
      auto out = impl();
      DEBUG_NORM(0, "out: ", out);
      return out;
    }
    template<class NumTraits>
    Option<AlascaLiteral<NumTraits>> normalize(Literal* l)
    { return tryNormalizeInterpreted<NumTraits>(l); }

    Option<AnyAlascaLiteral> tryNormalizeInterpreted(Literal* lit) const
    {
      using Out = AnyAlascaLiteral;
      auto wrapCoproduct = [](auto&& norm) {
        return std::move(norm).map([](auto x) { return Out(x); });
      };
      return             wrapCoproduct(tryNormalizeInterpreted< IntTraits>(lit))
        || [&](){ return wrapCoproduct(tryNormalizeInterpreted< RatTraits>(lit)); }
        || [&](){ return wrapCoproduct(tryNormalizeInterpreted<RealTraits>(lit)); }
        || Option<Out>();
    }

    Literal* normalizedLiteral(Literal* lit) const
    {
      auto interpreted = tryNumTraits([&](auto numTraits) {
          return tryNormalizeInterpreted<decltype(numTraits)>(lit)
            .map([](auto lit) { return lit.denormalize(); });
        });
      auto out = interpreted.isSome() ? *interpreted : normalizeUninterpreted(lit);
      DEBUG_NORM(0, *lit, " ==> ", *out)
      return out;
    }

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
      // TODO RStack
      Stack<TermList> args(lit->arity());
      args.loadFromIterator(typeArgIter(lit));
      for (auto orig : termArgIter(lit)) {
        args.push(normalize(orig).denormalize());
      }
      auto out = Literal::create(lit, args.begin());
      DEBUG_NORM(0, *lit, " ==> ", *out)
      return out;
    }
  };


} // namespace Kernel

#endif // __ALASCA_Normalization__

