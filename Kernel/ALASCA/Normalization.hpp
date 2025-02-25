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
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/STL.hpp"
// TODO remove(?)
#include "Inferences/PolynomialEvaluation.hpp"

#define DEBUG_NORM(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
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

