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
 * Defines functions and structres that are shared by all ALASCA inference rules in order to select literals, terms, etc.
 */

#ifndef __ALASCA_SelectionPrimitives__
#define __ALASCA_SelectionPrimitives__

#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Kernel/Clause.hpp"

namespace Kernel {

  using Inferences::PolynomialEvaluation;
  using Kernel::AnyAlascaLiteral;

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
    { return alascaLiteral()
          .apply([this](auto& lit) 
              { return AnyConstantType(lit.term().summandAt(_term).numeral); }); }

    template<class NumTraits>
    bool numTraitsIs() const 
    { return numeral().is<typename NumTraits::ConstantType>(); }

    template<class NumTraits>
    auto numeral() const 
    { return numeral().unwrap<typename NumTraits::ConstantType>(); }

    auto nContextTerms() const 
    { return alascaLiteral().apply([](auto& lit) { return lit.term().nSummands() - 1; }); }

    AnyAlascaLiteral const& alascaLiteral() const
    { return interpreted.unwrap(); }

    template<class NumTraits>
    auto const& alascaLiteral() const
    { return alascaLiteral().template unwrap<AlascaLiteral<NumTraits>>(); }

    template<class NumTraits>
    auto contextTerms() const 
    { 
      auto& lit = alascaLiteral<NumTraits>();
      return range(0, lit.term().nSummands()) 
                .filter([&](unsigned i) { return i != _term; })
                .map([&](unsigned i) { return lit.term().summandAt(i); });
    }

    TermList notSelectedTerm(AlascaLiteral<IntTraits> const& lit) const { ASSERTION_VIOLATION }

    template<class NumTraits>
    TermList notSelectedTerm(AlascaLiteral<NumTraits> const& lit) const { 
      return TermList(AlascaSignature<NumTraits>::sum(range(0, lit.term().nSummands()) 
                .filter([&](unsigned i) { return i != _term; })
                .map([&](unsigned i) { return lit.term().summandAt(i) / numeral<NumTraits>().abs(); })
                .map([&](auto t) { return t.denormalize(); })
            ));
    }

    // TODO use this everywhere possible
    auto notSelectedTerm() const 
    { return alascaLiteral()
        .apply([this](auto& x) { return notSelectedTerm(x); }); }

    bool isInequality() const
    { return alascaLiteral().apply([](auto& lit)
                               { return lit.isInequality(); }); }

    bool isIsInt() const
    { return alascaLiteral().apply([](auto& lit)
                               { return lit.isIsInt(); }); }

    TermList selectedAtom() const
    { return alascaLiteral()
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
    { return alascaLiteral().apply([](auto& l) { return l.symbol(); }); }

    TypedTermList key() const { return TypedTermList(selectedAtom(), sort()); }

    friend std::ostream& operator<<(std::ostream& out, SelectedSummand const& self);

    auto asTuple() const
    { return std::tie(_term, (SelectedLiteral const&)*this); }

    IMPL_COMPARISONS_FROM_TUPLE(SelectedSummand)

    friend std::ostream& operator<<(std::ostream& out, SelectedSummand const& self)
    { 
      self.numeral().apply([&](auto n) -> void { out << n; });
      out << " " << self.selectedAtom();
      self.numTraits()
        .apply([&](auto numTraits) {
          for (auto s : self.contextTerms<decltype(numTraits)>()) {
            out << " + " << s;
          }
        });
      out << " " << self.symbol() << " 0";
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << *l;
      }
      return out; 
    }
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
                   using ASig = AlascaSignature<decltype(numTraits)>;
                   using NumTraits = decltype(numTraits);
                   auto k = sel.numeral<NumTraits>();
                   return ASig::sum(sel.contextTerms<NumTraits>()
                        .map([&](auto monom) { return (monom / (-k)).denormalize();  }));
                });
            });
        },
        [](SelectedIntegerEquality       const& x) { return x.smallerSide(); },
        [](SelectedUninterpretedEquality const& x) { return x.smallerSide(); }); }

    auto contextLiterals() const
    { return _inner.apply([](auto& x) { return x.contextLiterals(); }); }

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

  using SelectionCriterion = OrderingUtils::SelectionCriterion;

} // namespace Kernel
 
#endif // __ALASCA_SelectionPrimitives__

