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

#include "Debug/Assertion.hpp"
#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/TypeList.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Kernel {

  using Kernel::AlascaLiteralItpAny;

  struct AlascaState;
  using UwaSubstitution = Coproduct<RobSubstitution, Indexing::ResultSubstitutionSP>; 

  struct SelectedLiteral {
    Clause* cl;
    unsigned litIdx;
    Option<AlascaLiteralItpAny> interpreted;

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



  class SelectedAtomicLiteral {
    Clause* _clause;
    unsigned _lit;
    using Self = SelectedAtomicLiteral;
    auto asTuple() const { return std::tie(_clause, _lit); }
  public:
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self);
    // TODO 1
    // { return ; }
  };

  class SelectedAtomicTermUF {
    Clause* _clause;
    unsigned _lit;
    unsigned _summand;
    using Self = SelectedAtomicTermUF;
    auto asTuple() const { return std::tie(_clause, _lit, _summand); }
  public:
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self);
    TypedTermList selectedAtomicTerm() const;
    // TODO 1
  };

  template<class NumTraits>
  class SelectedAtomicTermItp {
    Clause* _clause;
    unsigned _lit;
    unsigned _summand;
    using Self = SelectedAtomicTermItp;
    auto asTuple() const { return std::tie(_clause, _lit, _summand); }
  public:
    auto numTraits() const { return NumTraits {}; }
    using Numeral = typename NumTraits::ConstantType;
    bool isInequality() const;
    AlascaMonom<NumTraits> selected() const;
    // TODO 1 remove
    TypedTermList selectedAtom() const;
    TypedTermList selectedAtomicTerm() const;
    Numeral numeral() const;

    Clause* clause() const { return _clause; }
    Literal* literal() const { return (*_clause)[_lit]; }

    AlascaLiteralItp<NumTraits> alascaLiteral() const;
    unsigned litIdx() const { return _lit; }
    unsigned termIdx() const { return _summand; }
    IterTraits<VirtualIterator<Literal*>> contextLiterals() const;
    // TODO 1.3 do we actually want to use this?
    IterTraits<VirtualIterator<AlascaMonom<NumTraits>>> contextTerms() const;
    TermList contextTermSum() const;

    auto symbol() const { return alascaLiteral().symbol(); }
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self);
    // TODO 1
  };

  struct SelectedAtomicTerm 
    : public TypeList::ApplyT<Coproduct, 
               TypeList::Concat<
                   TypeList::MapT<SelectedAtomicTermItp, NumTraitsList>
                 , TypeList::List<SelectedAtomicTermUF>
               >>
  {

    Clause* clause() const;
    Literal* literal() const;
    unsigned litIdx() const;
    unsigned termIdx() const;

    IterTraits<VirtualIterator<Literal*>> contextLiterals() const;
    TypedTermList selectedAtomicTerm() const;
    using Self = SelectedAtomicTerm;
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { self.apply([&](auto& x) { out << x; }); return out; }
  };

  struct SelectedAtomicTermItpAny : public NumTraitsCopro<SelectedAtomicTermItp>
  {

    unsigned litIdx() const;
    unsigned termIdx() const;
    auto numTraits() const { return applyCo([](auto& x) { return x.numTraits(); }); }
    bool isInequality() const;
    TypedTermList selectedAtomicTerm() const { return apply([](auto x) { return x.selectedAtomicTerm(); }); }

    IterTraits<VirtualIterator<Literal*>> contextLiterals() const;
    Sign sign() const;
    Literal* literal() const;
    Clause* clause() const;
  };

  class SelectedEquality 
    : public SelectedAtomicTerm 
  {
    SelectedEquality(SelectedAtomicTerm self) : SelectedAtomicTerm(std::move(self)) {}
    static TypedTermList biggerSide(SelectedAtomicTermUF);
    static TermList smallerSide(SelectedAtomicTermUF);

    template<class C>
    static TermList div(IntTraits, TermList const& l, C const& r) 
    { return IntTraits::quotientF(l, IntTraits::constantTl(r)); }

    template<class NumTraits, class C>
    static TermList div(NumTraits, TermList const& l, C const& r) 
    { return NumTraits::linMul(1 / r, l); }
    // { return NumTraits::div(l, NumTraits::constantTl(r)); }

    template<class NumTraits>
    static TermList smallerSide(SelectedAtomicTermItp<NumTraits> const& l) 
    { return div(NumTraits{}, l.contextTermSum(), l.numeral()); }
  public:
    static Option<SelectedEquality> from(SelectedAtomicTerm self) {
      if (self.literal()->isEquality()) {
        return some(SelectedEquality(std::move(self)));
      } else {
        return {};
      }
    }
    bool positive() const;
    TypedTermList key() const { return biggerSide(); }

   
    TypedTermList biggerSide() const { return apply([](auto& x) { return x.selectedAtomicTerm(); }); }
    TermList smallerSide() const { return apply([](auto x) { return smallerSide(x); }); }

  };

  struct NewSelectedAtom : Coproduct<SelectedAtomicTerm, SelectedAtomicLiteral> {
    // using Coproduct::Coproduct;
    // TODO 1
    bool inLitPlus() const;
    IterTraits<VirtualIterator<AnyAlascaTerm>> iterBottomUp() const;
    Literal* literal() const;
    AlascaLiteral alascaLiteral() const;
    IterTraits<VirtualIterator<Literal*>> contextLiterals() const;
    Clause* clause() const;

    TermList selectedAtomicTerm() const;
  };

  using SelectionCriterion = OrderingUtils::SelectionCriterion;

} // namespace Kernel
  //
// TODO optimize normalizations of sorts; we do not normalize them
 
#endif // __ALASCA_SelectionPrimitives__

