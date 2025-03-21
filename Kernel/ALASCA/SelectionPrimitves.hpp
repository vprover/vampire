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

  class __SelectedLiteral {
    Clause* cl;
    unsigned lit;

  public:
    __SelectedLiteral(Clause* cl, unsigned lit) : cl(cl), lit(lit) {}

    Literal* literal() const { return (*cl)[lit]; }
    Clause* clause() const { return cl; }
    unsigned litIdx() const { return lit; }

    auto contextLiterals() const
      // TODO knownSize
    { return range(0, clause()->size())
              .filter([&](auto i) { return i != lit; }) 
              .map([&](auto i) { return (*clause())[i]; }); }
              
    auto asTuple() const
    { return std::make_tuple(cl, lit); }

    IMPL_COMPARISONS_FROM_TUPLE(__SelectedLiteral)
    IMPL_HASH_FROM_TUPLE(__SelectedLiteral)

    template<class C>
    std::ostream& output(std::ostream& out, C const& mainLiteral) const
    { 
      if (cl->size() == 1) {
        return out << mainLiteral;
      } else if (cl->size() == 0) {
        return out << "[]";
      } else {
        return out << 
          Output::catOwned(
              Output::cat(mainLiteral),
              "\\/",
              Output::interleaved("\\/", 
                contextLiterals().map([](auto l) { return Output::ptr(l); })) );
      }
    }


    friend std::ostream& operator<<(std::ostream& out, __SelectedLiteral const& self)
    { return self.output(out, Output::ptr(self.literal())); }
  };


  class SelectedAtomicLiteral 
    : public __SelectedLiteral  
  {
  };

  class SelectedAtomicTermUF 
    : public __SelectedLiteral  
  {
    bool _idx;
    using Self = SelectedAtomicTermUF;
    auto asTuple() const { return std::tie((__SelectedLiteral const&) *this, _idx); }
  public:
    SelectedAtomicTermUF(Clause* c, unsigned l, bool idx) 
      : __SelectedLiteral(c,l)
      , _idx(idx) 
    { ASS(literal()->isEquality()) }

    unsigned termIdx() const { return unsigned(_idx); }

    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { return self.output(out, Output::catOwned(
          self.biggerSide(), 
          self.literal()->isPositive() ? "=" : "!=", 
          self.smallerSide()  )); }
    TypedTermList selectedAtomicTerm() const { return biggerSide(); }
    TypedTermList biggerSide() const { return TypedTermList(literal()->termArg(unsigned(_idx)), literal()->eqArgSort()); }
    TermList smallerSide() const { return literal()->termArg(unsigned(_idx)); }
  };

  template<class NumTraits>
  class SelectedAtomicTermItp 
    : public __SelectedLiteral
  {
    unsigned _summand;
    using Self = SelectedAtomicTermItp;
    auto asTuple() const { return std::tie((__SelectedLiteral const&) *this, _summand); }
  public:
    auto numTraits() const { return NumTraits {}; }
    using Numeral = typename NumTraits::ConstantType;
    bool isInequality() const { return Kernel::isInequality(alascaLiteral().symbol()); }
    [[deprecated("bla")]]
    AlascaMonom<NumTraits> selected() const;
    AlascaMonom<NumTraits> selectedSummand() const;
    // TODO 1 remove
    TypedTermList selectedAtom() const;
    TypedTermList selectedAtomicTerm() const { return TypedTermList(selectedSummand().atom(), NumTraits::sort()); }
    Numeral numeral() const { return selectedSummand().numeral(); }
    Sign sign() const { return numeral().sign(); }

    // TODO 3 cache normalization result?
    AlascaLiteralItp<NumTraits> alascaLiteral() const { return InequalityNormalizer::normalize<NumTraits>(literal()).unwrap(); }
    unsigned termIdx() const { return _summand; }
    // TODO 1.3 do we actually want to use this?
    auto contextTerms() const {
      auto l = alascaLiteral();
      return concatIters(range(0, _summand), 
                         range(_summand + 1, l.term().nSummands()))
        .map([l](auto i) { return l.term().summandAt(i); });
    }
    TermList contextTermSum() const { return NumTraits::sum(contextTerms().map([](auto x) { return x.toTerm(); })); }

    auto symbol() const { return alascaLiteral().symbol(); }
    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self)
    { 
      auto l = self.alascaLiteral();
      ASS(l.term().nSummands() > 0)
      if (l.term().nSummands() == 1) {
        return self.output(out, Output::cat(self.selectedSummand(), l.symbol(), "0"));
      } else {
        return self.output(out, Output::cat(self.selectedSummand(), " + ", self.contextTerms().output(" + "), l.symbol(), "0"));
      }
    }
  };

  struct SelectedAtomicTerm 
    : public TypeList::ApplyT<Coproduct, 
               TypeList::Concat<
                   TypeList::MapT<SelectedAtomicTermItp, NumTraitsList>
                 , TypeList::List<SelectedAtomicTermUF>
               >>
  {
#define DELEGATE(fun) \
    auto fun() const { return apply([](auto& self) { return self.fun(); }); }

    DELEGATE(clause)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(termIdx)
    DELEGATE(selectedAtomicTerm)
    DELEGATE(contextLiterals)


    using Self = SelectedAtomicTerm;
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { self.apply([&](auto& x) { out << x; }); return out; }
  };

  struct SelectedAtomicTermItpAny : public NumTraitsCopro<SelectedAtomicTermItp>
  {

    DELEGATE(clause)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)

    DELEGATE(selectedAtomicTerm)
    DELEGATE(isInequality)
    DELEGATE(sign)
    DELEGATE(termIdx)

    auto numTraits() const 
    { return applyCo([](auto& x) { return x.numTraits(); }); }

  };

  class SelectedEquality 
    : public SelectedAtomicTerm 
  {
    SelectedEquality(SelectedAtomicTerm self) : SelectedAtomicTerm(std::move(self)) {}

    static TermList smallerSide(SelectedAtomicTermUF const& self) 
    { return self.smallerSide(); }

    template<class C>
    static TermList div(IntTraits, TermList const& l, C const& r) 
    { return IntTraits::quotientF(l, IntTraits::constantTl(r)); }

    template<class NumTraits, class C>
    static TermList div(NumTraits, TermList const& l, C const& r) 
    { return NumTraits::linMul(1 / r, l); }

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
    bool positive() const { return literal()->isPositive(); }
    TypedTermList key() const { return biggerSide(); }
   
    TypedTermList biggerSide() const { return apply([](auto& x) { return x.selectedAtomicTerm(); }); }
    TermList smallerSide() const { return apply([](auto x) { return smallerSide(x); }); }
  };

  struct NewSelectedAtom : Coproduct<SelectedAtomicTerm, SelectedAtomicLiteral> {
    // using Coproduct::Coproduct;
    // TODO 1
    bool inLitPlus() const;
    IterTraits<VirtualIterator<AnyAlascaTerm>> iterBottomUp() const;

    DELEGATE(clause)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)
  };
#undef DELEGATE

  using SelectionCriterion = OrderingUtils::SelectionCriterion;

} // namespace Kernel
  //
// TODO optimize normalizations of sorts; we do not normalize them
 
#endif // __ALASCA_SelectionPrimitives__

