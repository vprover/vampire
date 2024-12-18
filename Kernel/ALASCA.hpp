/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ALASCA.cpp
 * Defines all functionality shared among the components of the inequality resolution calculus.
 *
 */

#ifndef __ALASCA__
#define __ALASCA__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/STL.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Polynomial.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/OrderingUtils.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)


namespace Kernel {
  using Inferences::PolynomialEvaluation;

  enum class AlascaPredicate {
    EQ,
    NEQ,
    GREATER,
    GREATER_EQ,
  };

  template<class NumTraits>
  Literal* AlascaPredicateCreateLiteral(AlascaPredicate p, TermList t)
  { 
    switch(p) {
      case AlascaPredicate::EQ: return Literal::createEquality(true, t, NumTraits::zero(), NumTraits::sort());
      case AlascaPredicate::NEQ: return Literal::createEquality(false, t, NumTraits::zero(), NumTraits::sort());
      case AlascaPredicate::GREATER_EQ: return NumTraits::geq(true, t, NumTraits::zero());
      case AlascaPredicate::GREATER: return NumTraits::greater(true, t, NumTraits::zero());
    }
    ASSERTION_VIOLATION
  }

  /** returns true iff the predicate is > or >= */
  bool isInequality(AlascaPredicate const& self);

  template<class NumTraits>
  Literal* createLiteral(AlascaPredicate self, TermList t)
  {
    switch(self) {
      case AlascaPredicate::EQ: return NumTraits::eq(true, t, NumTraits::zero());
      case AlascaPredicate::NEQ: return NumTraits::eq(false, t, NumTraits::zero());
      case AlascaPredicate::GREATER: return NumTraits::greater(true, t, NumTraits::zero());
      case AlascaPredicate::GREATER_EQ: return NumTraits::geq(true, t, NumTraits::zero());
    }
    ASSERTION_VIOLATION
  }
  bool isIsInt(AlascaPredicate const& self);

  std::ostream& operator<<(std::ostream& out, AlascaPredicate const& self);

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
    friend struct std::hash<AlascaLiteral>;

  public:

    AlascaLiteral(Perfect<Polynom<NumTraits>> term, AlascaPredicate symbol) 
      : _term(term), _symbol(symbol) 
    { _term->integrity(); }

    friend class InequalityNormalizer;

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
    {
      auto l = term().denormalize();
      switch(symbol()) {
        case AlascaPredicate::EQ:  return NumTraits::eq(true, l, NumTraits::zero());
        case AlascaPredicate::NEQ: return NumTraits::eq(false, l, NumTraits::zero());
        case AlascaPredicate::GREATER: return NumTraits::greater(true, l, NumTraits::zero());
        case AlascaPredicate::GREATER_EQ: return NumTraits::geq(true, l, NumTraits::zero());
      }
      ASSERTION_VIOLATION
    }

    bool isInequality() const
    { return Kernel::isInequality(symbol()); }

    bool isIsInt() const
    { return Kernel::isIsInt(symbol()); }

    friend bool operator==(AlascaLiteral const& lhs, AlascaLiteral const& rhs)
    { return std::tie(lhs._symbol, lhs._term) ==  std::tie(rhs._symbol, rhs._term); }
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
  Option<InequalityLiteral<NumTraits>> inequalityLiteral(AlascaLiteral<NumTraits> lit) 
  {
    return lit.isInequality() ? some(InequalityLiteral<NumTraits>(lit)) 
                              : Option<InequalityLiteral<NumTraits>>();
  }

  class InequalityNormalizer {
    PolynomialEvaluation _eval;
    const bool _strong;

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

    /** param strong enables rewrites 
     * t >= 0 ==> t > 0 \/ t == 0
     * t != 0 ==> t > 0 \/ -t > 0
     */
    InequalityNormalizer(bool strong)
      : _strong(strong) {  }

    PolyNf normalize(TypedTermList term)
    { 
      TIME_TRACE("alasca normalize term")
      auto norm = PolyNf::normalize(term);
      auto out = _eval.evaluate(norm); 
      return out || norm;
    }

    PolyNf normalize(TermList t) 
    { return t.isTerm() ? normalize(t.term())
                        : PolyNf(Variable(t.var())); }

    template<class NumTraits> Option<Stack<AlascaLiteral<NumTraits>>> normalizeAlasca(Literal* lit) const;
    template<class NumTraits> Option<AlascaLiteral<NumTraits>> renormalizeAlasca(Literal* lit) const;
    template<class NumTraits> Option<InequalityLiteral<NumTraits>> renormalizeIneq(Literal* lit) const;


    template<class NumTraits> Option<AlascaLiteral<NumTraits>> renormalize(Literal* l)
    {
      auto norm = renormalizeAlasca<NumTraits>(l);
      if (norm.isNone()) {
        return Option<AlascaLiteral<NumTraits>>();
      } else {
        return Option<AlascaLiteral<NumTraits>>(norm.unwrap());
      }
    }

    Option<AnyAlascaLiteral> renormalize(Literal* lit) const;
    Option<AnyInequalityLiteral> renormalizeIneq(Literal*);


    // Literal* renormalizeLiteral(Literal* lit) const;
    Recycled<Stack<Literal*>> normalizeLiteral(Literal* lit) const;

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
       auto s1 = normalizeLiteral(lhs);
       auto s2 = normalizeLiteral(rhs);
       return s1 == s2;
     }

    bool equivalent(TypedTermList lhs, TypedTermList rhs) 
     { return normalize(lhs) == normalize(rhs); }


  private: 
    Literal* normalizeUninterpreted(Literal* lit) const;
  };

  struct AlascaState;
  using UwaSubstitution = Coproduct<RobSubstitution, Indexing::ResultSubstitutionSP>; 

  struct SelectedLiteral {
    Clause* cl;
    unsigned litIdx;
    Option<AnyAlascaLiteral> interpreted;

    SelectedLiteral(Clause* cl, unsigned litIdx, AlascaState& shared);

    Literal* literal() const { return (*cl)[litIdx]; }
    Clause* clause() const { return cl; }

    Option<AlascaPredicate> alascaPredicate() const {
      return interpreted.map([](auto& x) {
          return x.apply([](auto& x){ return x.symbol(); });
      });
    }


    auto contextLiterals() const
    { return range(0, clause()->size())
              .filter([&](auto i) { return i != litIdx; }) 
              .map([&](auto i) { return (*clause())[i]; }); }
              
    auto asTuple() const
    { return std::make_tuple(cl->number(), litIdx); }

    IMPL_COMPARISONS_FROM_TUPLE(SelectedLiteral)

    friend std::ostream& operator<<(std::ostream& out, SelectedLiteral const& self)
    { return out << Output::interleaved("\\/", concatIters(iterItems(self.literal()), self.contextLiterals()).map([](auto l) { return Output::ptr(l); })); }
  };


  class SelectedUninterpretedEquality : public SelectedLiteral
  {
    unsigned _term;
   public:
    SelectedUninterpretedEquality(SelectedLiteral lit, unsigned term) 
      : SelectedLiteral(std::move(lit))
      , _term(term)
    { 
      ASS(interpreted.isNone())
      ASS(literal()->isEquality())
      ASS(_term <= 1)
    }

    TermList biggerSide() const
    { return literal()->termArg(_term); }

    TermList smallerSide() const
    { return literal()->termArg(1 - _term); }

    TermList selectedAtom() const
    { return biggerSide(); }

    auto asTuple() const { return std::tie(_term, (SelectedLiteral const&) *this); }
    IMPL_COMPARISONS_FROM_TUPLE(SelectedUninterpretedEquality)
  };

  class SelectedSummand : public SelectedLiteral
  {
    unsigned _term;
  public:

    SelectedSummand(
      SelectedLiteral lit,
      unsigned term
    ) : SelectedLiteral(std::move(lit))
      , _term(term) 
    {
      ASS(interpreted.isSome())
    }

    auto termIdx() const { return _term; }

    auto numeral() const 
    { return ircLiteral()
          .apply([this](auto& lit) 
              { return AnyConstantType(lit.term().summandAt(_term).numeral); }); }

    template<class NumTraits>
    auto numeral() const 
    { return numeral().unwrap<typename NumTraits::ConstantType>(); }

    auto nContextTerms() const 
    { return ircLiteral().apply([](auto& lit) { return lit.term().nSummands() - 1; }); }

    AnyAlascaLiteral const& ircLiteral() const
    { return interpreted.unwrap(); }

    template<class NumTraits>
    auto const& ircLiteral() const
    { return ircLiteral().template unwrap<AlascaLiteral<NumTraits>>(); }

    template<class NumTraits>
    auto contextTerms() const 
    { 
      auto& lit = ircLiteral<NumTraits>();
      return range(0, lit.term().nSummands()) 
                .filter([&](unsigned i) { return i != _term; })
                .map([&](unsigned i) { return lit.term().summandAt(i); });
    }

    TermList notSelectedTerm(AlascaLiteral<IntTraits> const& lit) const { ASSERTION_VIOLATION }

    template<class NumTraits>
    TermList notSelectedTerm(AlascaLiteral<NumTraits> const& lit) const { 
      return TermList(NumTraits::sum(range(0, lit.term().nSummands()) 
                .filter([&](unsigned i) { return i != _term; })
                .map([&](unsigned i) { return lit.term().summandAt(i) / numeral<NumTraits>().abs(); })
                .map([&](auto t) { return t.denormalize(); })
            ));
    }

    // TODO use this everywhere possible
    auto notSelectedTerm() const 
    { return ircLiteral()
        .apply([this](auto& x) { return notSelectedTerm(x); }); }

    bool isInequality() const
    { return ircLiteral().apply([](auto& lit)
                               { return lit.isInequality(); }); }

    bool isIsInt() const
    { return ircLiteral().apply([](auto& lit)
                               { return lit.isIsInt(); }); }

    TermList selectedAtom() const
    { return ircLiteral()
          .apply([this](auto& lit) 
              { return lit.term().summandAt(_term).factors->denormalize(); }); }

    auto sign() const 
    { return numeral().apply([](auto const& self) { return self.sign(); }); }

    auto numTraits() const 
    { return numeral().apply([](auto n) 
        { return Coproduct<IntTraits, RatTraits, RealTraits>(NumTraits<decltype(n)>{}); });
    }

    TermList sort() const { return numTraits().apply([](auto num) { return num.sort(); });  }

    auto symbol() const
    { return ircLiteral().apply([](auto& l) { return l.symbol(); }); }

    TypedTermList key() const { return TypedTermList(selectedAtom(), sort()); }

    friend std::ostream& operator<<(std::ostream& out, SelectedSummand const& self);

    auto asTuple() const
    { return std::tie(_term, (SelectedLiteral const&)*this); }

    IMPL_COMPARISONS_FROM_TUPLE(SelectedSummand)
  };

  class SelectedAtom: public Coproduct<SelectedUninterpretedEquality, SelectedSummand>
  {
    using Super = Coproduct<SelectedUninterpretedEquality, SelectedSummand>;
    public:
      SelectedAtom(SelectedUninterpretedEquality e) : Super(std::move(e)) {}
      SelectedAtom(SelectedSummand               e) : Super(std::move(e)) {}

      TermList atom()
      { return apply([](auto& self) { return self.selectedAtom(); }); }
  };


  class SelectedIntegerEquality : public SelectedSummand 
  {
  public:
    SelectedIntegerEquality(SelectedSummand s) 
      : SelectedSummand(std::move(s)) 
    { ASS(numTraits() == decltype(numTraits())(IntTraits{})) }

    TermList biggerSide() const 
    { return IntTraits::mulSimpl(numeral<IntTraits>(), selectedAtom()); }

    TermList smallerSide() const 
    { return IntTraits::sum(contextTerms<IntTraits>().map([](auto t) { return (-t).denormalize(); })); }

    // friend std::ostream& operator<<(std::ostream& out, SelectedIntegerEquality const& self)
    // { return out << (SelectedSummand const&)self; }

  };

  class SelectedEquality 
  {
    Coproduct<SelectedSummand, SelectedIntegerEquality, SelectedUninterpretedEquality>  _inner;

  public:

    explicit SelectedEquality(SelectedSummand s) 
      : _inner(decltype(_inner)::variant<0>(std::move(s))) 
    { 
      ASS(!_inner.unwrap<0>().isInequality()) 
      ASS(_inner.unwrap<0>().numTraits().apply([](auto x) { return x.isFractional(); }))
    }

    TermList selectedAtom() const
    { return biggerSide(); }

    explicit SelectedEquality(SelectedIntegerEquality s) 
      : _inner(decltype(_inner)::variant<1>(std::move(s))) 
    { 
    }

    explicit SelectedEquality(SelectedUninterpretedEquality s) 
      : _inner(decltype(_inner)(std::move(s))) {}

    Clause* clause() const 
    { return _inner.apply([](auto& x) { return x.clause(); }); }

    unsigned litIdx() const 
    { return _inner.apply([](auto& x) { return x.litIdx; }); }

    bool positive() const 
    { return literal()->isPositive(); }

    bool isFracNum() const
    { 
      ASS(!_inner.template is<SelectedSummand>() 
        || _inner.template unwrap<SelectedSummand>().numTraits().apply([](auto x) { return x.isFractional(); }))
      return _inner.template is<SelectedSummand>(); 
    }

    TypedTermList biggerSide() const 
    { return TypedTermList(
        _inner.match(
          [](SelectedSummand               const& x) { return x.selectedAtom(); },
          [](SelectedIntegerEquality       const& x) { return x.biggerSide(); },
          [](SelectedUninterpretedEquality const& x) { return x.biggerSide(); }), 
        SortHelper::getEqualityArgumentSort(literal())); }

    TermList smallerSide() const 
    { return _inner.match(
        [&](SelectedSummand               const& sel) 
        { return sel.numTraits().apply([&](auto numTraits) {
            return ifIntTraits(numTraits,
                [](IntTraits) -> TermList { ASSERTION_VIOLATION },
                [&](auto numTraits) {
                   using NumTraits = decltype(numTraits);
                   auto k = sel.numeral<NumTraits>();
                   return NumTraits::sum(sel.contextTerms<NumTraits>()
                        .map([&](auto monom) { return (monom / (-k)).denormalize();  }));
                });
            });
        },
        [](SelectedIntegerEquality       const& x) { return x.smallerSide(); },
        [](SelectedUninterpretedEquality const& x) { return x.smallerSide(); }); }

    auto contextLiterals() const
    { return _inner.apply([](auto& x) { return x.contextLiterals(); }); }
    // { return ifElseIter(
    //     _inner.is<0>(), 
    //     [&]() { return _inner.unwrap<0>().contextLiterals(); },
    //     // else
    //     [&]() { return _inner.unwrap<1>().contextLiterals(); }); }


    Literal* literal() const
    { return _inner.apply([](auto& x) { return x.literal(); }); }

    TermList sort() const { return SortHelper::getEqualityArgumentSort(literal()); }
    TypedTermList key() const { return TypedTermList(biggerSide(), sort()); }

    friend std::ostream& operator<<(std::ostream& out, SelectedEquality const& self)
    { 
      out << self.biggerSide() << (self.positive() ? " = " : " != ") << self.smallerSide();
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << *l;
      }
      return out; 
    }

    auto asTuple() const { return std::tie(_inner); }
    IMPL_COMPARISONS_FROM_TUPLE(SelectedEquality)
  };
  class SelectedUninterpretedPredicate : public SelectedLiteral {
  public:
    SelectedUninterpretedPredicate(SelectedLiteral lit)
      : SelectedLiteral(std::move(lit))
    { 
      ASS(interpreted.isNone())
      ASS(!literal()->isEquality())
    }
  };
  using SelectionCriterion = OrderingUtils2::SelectionCriterion;
  struct AlascaState 
  {
    USE_ALLOCATOR(AlascaState);

    // TODO get rid of this
    static std::shared_ptr<AlascaState> globalState;

  private:
    AlascaState(
          std::shared_ptr<InequalityNormalizer> normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction uwa,
          bool fixedPointIteration
        )
      : _normalizer(std::move(normalizer))
      , ordering(std::move(ordering))
      , uwa(uwa) 
      , uwaFixedPointIteration(fixedPointIteration)
    {}

  public:
    std::shared_ptr<InequalityNormalizer> _normalizer;
    Ordering* const ordering;
    Shell::Options::UnificationWithAbstraction uwa;
    bool const uwaFixedPointIteration;

    InequalityNormalizer& norm() const { return *_normalizer; }
    std::shared_ptr<InequalityNormalizer> normalizerPtr() const { return _normalizer; }

    Shell::Options::UnificationWithAbstraction uwaMode() const { return uwa; }


    static std::shared_ptr<AlascaState> create(
          std::shared_ptr<InequalityNormalizer> normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction const uwa,
          bool const fixedPointIteration
        ) 
    {
      globalState = Lib::make_shared(AlascaState(std::move(normalizer), ordering, uwa, fixedPointIteration));
      return globalState;
    }

    bool isAtomic(Term* t) { return !interpretedFunction(t) || 
      forAnyNumTraits([&](auto n) { return n.isFloor(t->functor()); }); }
    bool isAtomic(TermList t) { return t.isTerm() && isAtomic(t.term()); }


    auto maxLits(Clause* cl, SelectionCriterion sel) {
      return OrderingUtils2::maxElems(
          cl->size(), 
          [=](unsigned l, unsigned r) 
          { return ordering->compare((*cl)[l], (*cl)[r]); },
          [=](unsigned i) -> Literal&
          { return *(*cl)[i]; },
          sel)
        .map([=](auto i) 
            { return SelectedLiteral(cl, i, *this); });
    }

    template<class LitOrTerm>
    bool greater(LitOrTerm lhs, LitOrTerm rhs)
    { return ordering->compare(lhs, rhs) == Ordering::Result::GREATER; }

    template<class LitOrTerm>
    bool notLess(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils2::notLess(ordering->compare(lhs, rhs)); }

    template<class LitOrTerm>
    bool notLeq(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils2::notLeq(ordering->compare(lhs, rhs)); }

    template<class NumTraits>
    auto maxSummandIndices(AlascaLiteral<NumTraits> const& lit, SelectionCriterion selection)
    {
        auto monomAt = [=](auto i) 
             { return lit.term().summandAt(i).factors->denormalize(); }; 

        return iterTraits(OrderingUtils2::maxElems(
                  lit.term().nSummands(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  [=](unsigned i)
                  { return monomAt(i); },
                  selection));
    }


    template<class T>
    auto maxSummandIndices(std::shared_ptr<T> const& sum, SelectionCriterion selection)
    { return maxSummandIndices(*sum, selection); }

    template<class T>
    auto maxSummandIndices(Recycled<T> const& sum, SelectionCriterion selection)
    { return maxSummandIndices(*sum, selection); }

    template<class Numeral>
    auto maxSummandIndices(Stack<std::pair<TermList, Numeral>> const& sum, SelectionCriterion selection)
    {
        auto monomAt = [=](auto i) 
             { return sum[i].first; }; 

        return iterTraits(OrderingUtils2::maxElems(
                  sum.size(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  [=](unsigned i)
                  { return monomAt(i); },
                  selection));
    }



    auto maxEqIndices(Literal* lit, SelectionCriterion sel)
    {
      Stack<unsigned> is(2);
      auto iter = [](std::initializer_list<unsigned> out)  
                  { return arrayIter(Stack<unsigned>(out)); };
      switch (sel) {
        case SelectionCriterion::STRICTLY_MAX:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});

            case Ordering::Result::EQUAL:
            case Ordering::Result::INCOMPARABLE: return iter({});
          }

        case SelectionCriterion::ANY:
          return iter({0,1});

        case SelectionCriterion::NOT_LESS:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});

            case Ordering::Result::EQUAL:
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }

        case SelectionCriterion::NOT_LEQ:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});
            case Ordering::Result::EQUAL:        return iter({});
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }
      }

      return arrayIter(std::move(is));
    }

    auto selectUninterpretedEquality(SelectedLiteral lit, SelectionCriterion sel)
    { return maxEqIndices(lit.literal(), sel)
        .map([lit](auto i) { return SelectedUninterpretedEquality(lit, i); }); }

    auto activePositions(Literal* l) -> IterTraits<VirtualIterator<TermList>>
    {
      return iterTraits(norm().renormalize(l)
        .match(
          [=](AnyAlascaLiteral l) -> VirtualIterator<TermList> {
            return pvi(coproductIter(std::move(l).applyCo([=](auto l)  {
                return maxSummandIndices(l, SelectionCriterion::NOT_LEQ)
                         .map([l](auto i) {
                             return l.term().summandAt(i).factors->denormalize();
                         });
            })));
          },
          [=]() {
            if (l->isEquality()) {
              return pvi(maxEqIndices(l, SelectionCriterion::NOT_LEQ)
                .map([=](auto i) { return l->termArg(i); }));
            } else {
                return pvi(termArgIter(l));
            }
          }));
    }


    bool subtermEqModT(TermList sub, TermList sup)
    {
      ASS(isAtomic(sub))
      // TODO add assertion that sub is an atomic term
      return norm().normalize(sup).denormalize()
        .containsSubterm(norm().normalize(sub).denormalize());
    }


    auto maxSummands(SelectedLiteral sel_lit , SelectionCriterion sel) 
    { return coproductIter(sel_lit.interpreted.unwrap()
                .applyCo([&](auto& lit) 
                       { return maxSummandIndices(lit, sel); }))
                .map([=](auto i) 
                     { return SelectedSummand(sel_lit, i); }); }


    auto selectedActivePositions(
        Clause* cl, SelectionCriterion selLit, 
        SelectionCriterion selSum,
        bool includeUnshieldedNumberVariables)
    {
      using Out = Coproduct<SelectedSummand, SelectedUninterpretedEquality, SelectedUninterpretedPredicate>;
      return maxLits(cl, selLit)
        .flatMap([=](auto sel_lit) -> VirtualIterator<Out> {
            auto lit = sel_lit.literal();
            if (sel_lit.interpreted.isSome()) {
              return pvi(maxSummands(sel_lit, selSum)
                  .filter([=](auto x) { return includeUnshieldedNumberVariables || x.numTraits().apply([](auto x) { return !x.isFractional(); }) || !x.selectedAtom().isVar(); })
                  .map([](auto x) { return Out(std::move(x)); }));

            } else if (lit->isEquality()) {
              return pvi(maxEqIndices(lit, selSum)
                        .map([=](auto j) 
                            { return Out(SelectedUninterpretedEquality(sel_lit, j)); }));
            } else {
              return pvi(getSingletonIterator(Out(SelectedUninterpretedPredicate(sel_lit))));
            }
        });
    }

    auto isUninterpreted(Literal* l) const 
    { return !l->isEquality() && norm().renormalize(l).isNone(); }

    auto selectedUninterpretedLiterals(Clause* cl, SelectionCriterion selLit) {
      return maxLits(cl, selLit)
        .filter([&](auto& lit) { return isUninterpreted(lit.literal()); });
    }


    auto selectedEqualities(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedEquality;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out>
                   { return x.match(
                       [](SelectedSummand& x) {
                          return x.isInequality() ? Option<Out>()
                              : x.numTraits().template is<IntTraits>() ? Option<Out>(Out(SelectedIntegerEquality(std::move(x))))
                              : Option<Out>(Out(std::move(x)));
                       },

                       [](SelectedUninterpretedEquality& x) 
                       { return Option<Out>(Out(std::move(x))); },

                       [](SelectedUninterpretedPredicate&) 
                       { return Option<Out>(); });
        });
    }


    bool interpretedFunction(TermList t) 
    { return t.isTerm() && interpretedFunction(t.term()); }

    bool interpretedFunction(Term* t) 
    { return forAnyNumTraits([&](auto numTraits) -> bool {
            return theory->isInterpretedFunction(t, numTraits.addI)
                || theory->isInterpretedFunction(t, numTraits.minusI)
                || theory->isInterpretedConstant(t)
                || (theory->isInterpretedFunction(t, numTraits.mulI)
                    && theory->isInterpretedConstant(t->termArg(0)));
      }); }

    // TODO move to AlascaUtils
    static bool interpretedPred(Literal* t) {
      auto f = t->functor();
      return t->isEquality()
        || forAnyNumTraits([&](auto numTraits) -> bool {
            return f == numTraits.geqF()
               ||  f == numTraits.greaterF()
               ||  f == numTraits.isIntF();
      });
    }

    bool isUninterpretedEquality(Literal* t) {
      return t->isEquality()
        && !forAnyNumTraits([&](auto numTraits) -> bool {
            return SortHelper::getEqualityArgumentSort(t) == numTraits.sort();
      });
    }


    auto maxAtoms(Clause* cl, SelectionCriterion criterion, bool includeUnshieldedNumberVariables) {
      using Out = SelectedAtom;
      auto atoms = Lib::make_shared(Stack<Out>());
      for (unsigned i : range(0, cl->size())) {
        auto l = SelectedLiteral(cl, i, *this);
        if (interpretedPred(l.literal())) {
          if (l.interpreted.isSome()) {
            for (auto a : maxSummands(l, criterion)) {
              atoms->push(Out(a));
            }
          } else {
            // must be an equality of uninterpreted terms
            ASS(isUninterpretedEquality(l.literal()));
            for (auto a : selectUninterpretedEquality(l, criterion)) {
              atoms->push(Out(a));
            }
          }
        } else {
          atoms = Lib::make_shared(Stack<Out>());
          break;
        }
      }

      return OrderingUtils2::maxElems(
          atoms->size(), 
          [=](unsigned l, unsigned r) 
          { return ordering->compare((*atoms)[l].atom(), (*atoms)[r].atom()); },
          [=](unsigned i)
          { return (*atoms)[i].atom(); },
          criterion)
        .map([=](auto i) 
            { return (*atoms)[i]; })
      .filter([=](auto x) 
          { return !x.template is<SelectedSummand>() 
                || !x.template unwrap<SelectedSummand>().selectedAtom().isVar(); });
    }


    auto selectedSummands(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedSummand;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out> {
            return x.match(
                 [](SelectedSummand& x) 
                 { return Option<Out>(std::move(x)); },

                 [](SelectedUninterpretedEquality&) 
                 { return Option<Out>(); },

                 [](SelectedUninterpretedPredicate&) 
                 { return Option<Out>(); });
        });
    }

  public:

    Option<AbstractingUnifier> unify(TermList lhs, TermList rhs) const;

    template<class LitOrTerm, class Iter>
    bool strictlyMaximal(LitOrTerm pivot, Iter lits)
    {
      bool found = false;
      for (auto lit : iterTraits(lits)) {
        if (lit == pivot) {
          if (found)  {
            return false;
          } else {
            found = true;
          }
        }
        if (ordering->compare(pivot, lit) == Ordering::LESS) {
          return false;
        }
      }
      ASS(found)
      return true;
    }
  };

#if VDEBUG
  std::shared_ptr<AlascaState> testAlascaState(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LPAR_MAIN,
    std::shared_ptr<InequalityNormalizer> strongNormalization = Lib::make_shared(InequalityNormalizer(/*strong*/ false)),
    Ordering* ordering = nullptr,
    bool uwaFixdPointIteration = false
    );
#endif

}

////////////////////////////////////////////////////////////////////////////
// impl InequalityLiteral
/////////////////////////////
  
namespace Kernel {

template<class NumTraits>
Option<InequalityLiteral<NumTraits>> InequalityNormalizer::renormalizeIneq(Literal* lit) const
{
  using Opt = Option<InequalityLiteral<NumTraits>>;
  return normalizeAlasca<NumTraits>(lit)
    .andThen([](auto lit) {
      // The literal must have been normalized before, hence normalizing again can't produce more than one literal
      ASS_EQ(lit.size(), 1) 
      if (lit[0].isInequality()) {
        return Opt(InequalityLiteral<NumTraits>(std::move(lit)));
      } else {
        return Opt();
      }
    });
}


template<class Numeral>
Numeral normalizeFactors_divide(Numeral gcd, Numeral toCorrect)  
{ return toCorrect / gcd; }

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect);

template<class Numeral>
Numeral normalizeFactors_gcd(Numeral l, Numeral r)
{
  return Numeral(l.numerator()  .gcd(r.numerator()),
                 l.denominator().lcm(r.denominator()));
}

IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r);

template<class NumTraits>
auto normalizeFactors(Perfect<Polynom<NumTraits>> in) -> Perfect<Polynom<NumTraits>>
{
  if (in->nSummands() == 0) {
    return in;
  }
  auto gcd = fold(in->iterSummands()
    .map([](auto s) { return s.numeral.abs(); }),
    [](auto l, auto r) { return normalizeFactors_gcd(l,r); }
  );
  ASS_REP(gcd >= NumTraits::constant(0), gcd)
  if (gcd == NumTraits::constant(1) || gcd == NumTraits::constant(0)) {
    return in;
  } else {
    auto  out = perfect(Polynom<NumTraits>(in->iterSummands()
          .map([=](auto s) { return Monom<NumTraits>(normalizeFactors_divide(gcd, s.numeral), s.factors); })
          .template collect<Stack>()));
    return out;
  }
}

template<class NumTraits>
Option<AlascaLiteral<NumTraits>> InequalityNormalizer::renormalizeAlasca(Literal* lit) const
{
  return normalizeAlasca<NumTraits>(lit)
    .map([](auto&& lits) -> AlascaLiteral<NumTraits> { 
        ASS_REP(lits.size() == 1, "literal has not been normalized before.");
        return std::move(lits[0]);
      });
}

template<class NumTraits>
Option<Stack<AlascaLiteral<NumTraits>>> InequalityNormalizer::normalizeAlasca(Literal* lit) const
{
  DEBUG("in: ", *lit, " (", NumTraits::name(), ")")
  using Numeral = typename NumTraits::ConstantType;

  auto impl = [&]() {

    constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

    using Opt = Option<Stack<AlascaLiteral<NumTraits>>>;

    auto f = lit->functor();
    if (!theory->isInterpretedPredicate(f))
      return Opt();

    auto itp = theory->interpretPredicate(f);

    AlascaPredicate pred;
    TermList l, r; // <- we rewrite to l < r or l <= r
    switch(itp) {
     
      case Interpretation::EQUAL:/* l == r or l != r */
        if (SortHelper::getEqualityArgumentSort(lit) != NumTraits::sort()) 
          return Opt();
        if (*lit->nthArgument(0) == NumTraits::zero()) {
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
        return Opt();
    }

    if (lit->isNegative() && isInequality(pred)) {
      // ~(l >= r) <==> (r < l)
      std::swap(l, r);
      pred = pred == AlascaPredicate::GREATER ? AlascaPredicate::GREATER_EQ : AlascaPredicate::GREATER;
    }

    if (isInt && pred == AlascaPredicate::GREATER_EQ) {
      /* l <= r ==> l < r + 1 */
      r = NumTraits::add(r, NumTraits::one());
      pred = AlascaPredicate::GREATER;
    }

    /* l < r ==> r > l ==> r - l > 0 */
    auto t = l == NumTraits::zero() ? r 
           : r == NumTraits::zero() ? NumTraits::minus(l)
           : NumTraits::add(r, NumTraits::minus(l));

    ASS(!isInt || pred != AlascaPredicate::GREATER_EQ)

    auto tt = TypedTermList(t, NumTraits::sort());
    auto norm = Kernel::normalizeTerm(tt);
    auto simpl = _eval.evaluate(norm);
    auto simplValue = (simpl || norm).wrapPoly<NumTraits>();
    simplValue->integrity();
    auto factorsNormalized = normalizeFactors(simplValue);
    switch(pred) {
      case AlascaPredicate::EQ:
      case AlascaPredicate::NEQ:
        // normalizing s == t <-> -s == -t
        if (factorsNormalized->nSummands() > 0) {
          if (factorsNormalized->summandAt(0).numeral < Numeral(0)) {
            factorsNormalized = perfect(-*factorsNormalized);
          }
        }
      case AlascaPredicate::GREATER:
      case AlascaPredicate::GREATER_EQ:
        break;
    }


    Stack<AlascaLiteral<NumTraits>> out;
    if (_strong && pred == AlascaPredicate::GREATER_EQ) {
      // t >= 0 ==> t > 0 \/ t == 0
      out = { AlascaLiteral<NumTraits>(factorsNormalized, AlascaPredicate::GREATER)
            , AlascaLiteral<NumTraits>(factorsNormalized, AlascaPredicate::EQ     ) };
    } else if (_strong && pred == AlascaPredicate::NEQ) {
      // t != 0 ==> t > 0 \/ -t > 0
      out = { AlascaLiteral<NumTraits>( factorsNormalized, AlascaPredicate::GREATER)
            , AlascaLiteral<NumTraits>(-factorsNormalized, AlascaPredicate::GREATER) };
    } else {
      out = { AlascaLiteral<NumTraits>(factorsNormalized, pred) };
    }

    return Opt(std::move(out));
  };
  auto out = impl();
  DEBUG("out: ", out);
  return out;
}


////////////////////////////////////////////////////////////////////////////
// impl AlascaState
/////////////////////////////

Ordering::Result compare(AlascaPredicate l, AlascaPredicate r);


class AlascaPreprocessor {
  Map<unsigned, unsigned> _preds;
  Map<unsigned, unsigned> _funcs;
  // TODO create option for this
  bool _useFloor = false;

  using Z = IntTraits;
  using R = RealTraits;
  // friend class IntegerConversionFT;
  static constexpr InferenceRule INF_RULE = InferenceRule::ALASCA_INTEGER_TRANSFORMATION;
  Literal* integerConversion(Literal* unit); 
  TermList integerConversion(TypedTermList t); 
  unsigned integerPredicateConversion(unsigned f); 
  unsigned integerFunctionConversion(unsigned f); 
  unsigned integerTypeConsConversion(unsigned f); 
  Clause* integerConversion(Clause* unit); 
  // FormulaUnit* integerConversion(FormulaUnit* unit);
  Unit* integerConversion(Unit* unit) {
    ASS_REP(unit->isClause(), "integer conversion needs to be performed after clausification because we don't wanna deal with FOOL & friends here")
    return (Unit*)integerConversion(static_cast<Clause*>(unit));
    // return unit->isClause() 
    //   ? (Unit*)integerConversion(static_cast<Clause*>(unit))
    //   : (Unit*)integerConversion(static_cast<FormulaUnit*>(unit));
  }
public:
  AlascaPreprocessor() : _preds() {}
  void integerConversion(Problem& prb);
};

// TODO move somewhere else and use
template<class NumTraits, class F>
Option<std::invoke_result_t<F, AlascaPredicate, TermList, unsigned>> ifAlascaLiteral(Literal* lit, F f) {
  // TODO assert normalized
  if (NumTraits::isGreater(lit->functor())) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(AlascaPredicate::GREATER   , lit->termArg(0), 0));
  }
  if (NumTraits::isGeq(lit->functor())    ) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(AlascaPredicate::GREATER_EQ, lit->termArg(0), 0));
  }
  if (lit->isEquality() && SortHelper::getEqualityArgumentSort(lit) == NumTraits::sort()) {
    auto i = 0;
    if (auto n = NumTraits::tryNumeral(lit->termArg(0))) {
      if (*n == 0) {
        i++;
      }
    }
    return some(f(lit->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ, lit->termArg(i), i));
  }
  return {};
}

// TODO move somewhere else and use
template<class NumTraits, class T, class F>
auto ifNumMul(T term, F f) {
  return NumTraits::ifMul(term, [&](auto l, auto r) {
      ASS(!NumTraits::isNumeral(r))
      return NumTraits::ifNumeral(l, [&](auto l) { return f(l, r, 1); });
  }).flatten()
  .orElse([&](){
      return NumTraits::ifMinus(term, [&](auto t) { return  f(NumTraits::constant(-1), t, 0); });
      });
}

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isNumMul(T term) 
{ return ifNumMul<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isAlascaLiteral(T term) 
{ return ifAlascaLiteral<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO move somewhere else and use
template<class NumTraits, class T>
auto isUninterpreted(T t) 
{ return !NumTraits::isFloor(t) && !NumTraits::isAdd(t) && !isNumMul<NumTraits>(t); }


} // namespace Kernel

template<class NumTraits> struct std::hash<Kernel::AlascaLiteral<NumTraits>>
{
  size_t operator()(Kernel::AlascaLiteral<NumTraits> const& self) const
  {
    return Lib::HashUtils::combine(
      Lib::StlHash::hash(self._symbol),
      Lib::StlHash::hash(self._term)
    );
  }
};



#undef DEBUG
#endif // __ALASCA__

