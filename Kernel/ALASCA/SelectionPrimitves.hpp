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
#include "Kernel/NumTraits.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/TypeList.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Kernel {

  using Kernel::AlascaLiteralItpAny;
  using AlascaAtom = Coproduct<TypedTermList, Literal*>;

  struct AlascaState;
  using UwaSubstitution = Coproduct<RobSubstitution, Indexing::ResultSubstitutionSP>; 

  class __SelectedLiteral 
  {
    Clause* _cl;
    unsigned _lit;

  public:
    __SelectedLiteral(Clause* cl, unsigned lit) : _cl(cl), _lit(lit) {}

    Literal* literal() const { return (*_cl)[_lit]; }
    Clause* clause() const { return _cl; }
    unsigned litIdx() const { return _lit; }

    auto contextLiterals() const
    { return clause()->iterLits().cloned().dropNth(_lit); }
              
    auto asTuple() const
    { return std::make_tuple(_cl, _lit); }

    IMPL_COMPARISONS_FROM_TUPLE(__SelectedLiteral)
    IMPL_HASH_FROM_TUPLE(__SelectedLiteral)

    template<class C>
    std::ostream& output(std::ostream& out, C const& mainLiteral) const
    { 
      if (_cl->size() == 1) {
        return out << mainLiteral;
      } else if (_cl->size() == 0) {
        return out << "[]";
      } else {
        return out << 
          Output::catOwned(
              Output::cat(mainLiteral),
              "\\/",
              Output::interleaved("\\/", 
                contextLiterals().map([](auto l) { return Output::cat(*l); })) );
      }
    }


    friend std::ostream& operator<<(std::ostream& out, __SelectedLiteral const& self)
    { return self.output(out, Output::ptr(self.literal())); }
  };


  class SelectedAtomicLiteral 
    : public __SelectedLiteral  
  {
  public:
    using __SelectedLiteral::__SelectedLiteral;
    auto iterSelectedSubterms() const 
    { return termArgIterTyped(literal()) 
               .flatMap([](auto t) { return AnyAlascaTerm::normalize(t).bottomUpIter(); }); }
    bool productive() const { return literal()->isPositive(); }
    AlascaAtom selectedAtom() const { return AlascaAtom(literal()); }
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

    bool productive() const { return literal()->isPositive(); }

    auto iterSelectedSubterms() const 
    { return selectedAtomicAlascaTerm().bottomUpIter(); }

    IMPL_COMPARISONS_FROM_TUPLE(Self);
    IMPL_HASH_FROM_TUPLE(Self);
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { return self.output(out, Output::catOwned(
          self.biggerSide(), 
          self.literal()->isPositive() ? "=" : "!=", 
          self.smallerSide()  )); }
    TypedTermList selectedAtomicTerm() const { return biggerSide(); }
    AlascaAtom selectedAtom() const { return AlascaAtom(selectedAtomicTerm()); }
    AnyAlascaTerm selectedAtomicAlascaTerm() const { return AnyAlascaTerm::normalize(selectedAtomicTerm()); }
    TypedTermList biggerSide() const { return TypedTermList(literal()->termArg(unsigned(_idx)), literal()->eqArgSort()); }
    TermList smallerSide() const { return literal()->termArg(1 - unsigned(_idx)); }
  };

  template<class NumTraits>
  class SelectedAtomicTermItp 
    : public __SelectedLiteral
  {
    unsigned _summand;
    using Self = SelectedAtomicTermItp;
    auto asTuple() const { return std::tie((__SelectedLiteral const&) *this, _summand); }
  public:

    SelectedAtomicTermItp(Clause* cl, unsigned lit, unsigned summand) 
      : __SelectedLiteral(cl, lit)
      , _summand(summand)
    {  }

    auto numTraits() const { return NumTraits {}; }
    using Numeral = typename NumTraits::ConstantType;
    bool isInequality() const { return Kernel::isInequality(alascaLiteral().symbol()); }
    AlascaMonom<NumTraits> selectedSummand() const { return alascaLiteral().term().summandAt(_summand); }
    // TODO 1 remove
    TypedTermList selectedAtomicTerm() const { return TypedTermList(selectedSummand().atom(), NumTraits::sort()); }
    // TypedTermList selectedAtom() const { return selectedAtomicTerm(); }
    Coproduct<TypedTermList, Literal*> selectedAtom() const { return Coproduct<TypedTermList, Literal*>(selectedAtomicTerm()); }
    AnyAlascaTerm selectedAtomicAlascaTerm() const { return AnyAlascaTerm::normalize(selectedAtomicTerm()); }
    Numeral numeral() const { return selectedSummand().numeral(); }
    Sign sign() const { return numeral().sign(); }

    bool productive() const 
    { return isInequality() ? selectedSummand().numeral() > 0 
                            : literal()->isPositive(); }

    auto iterSelectedSubterms() const 
    { return selectedAtomicAlascaTerm().bottomUpIter(); }

    // TODO 3 cache normalization result?
    AlascaLiteralItp<NumTraits> alascaLiteral() const { return InequalityNormalizer::normalize<NumTraits>(literal()).unwrap(); }
    unsigned termIdx() const { return _summand; }
    // TODO 1.3 do we actually want to use this?
    auto contextTerms() const 
    { return alascaLiteral().term()
        .iterSummands()
        .dropNth(_summand); }

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
    using Coproduct::Coproduct;
#define DELEGATE(fun) \
    auto fun() const { return apply([](auto& self) { return self.fun(); }); }

#define DELEGATE_ITER(fun) \
    auto fun() const { return coproductIter(applyCo([](auto& self) { return self.fun(); })); }

    DELEGATE(clause)
    DELEGATE(productive)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(termIdx)
    DELEGATE(selectedAtomicTerm)
    DELEGATE(selectedAtom)
    DELEGATE(contextLiterals)
    DELEGATE(selectedAtomicAlascaTerm)
    DELEGATE(iterSelectedSubterms)

    template<class NumTraits>
    static bool isNumSort(SelectedAtomicTermItp<NumTraits> const&) { return true; }
    static bool isNumSort(SelectedAtomicTermUF const&) { return false; }
    bool isNumSort() const { return apply([](auto& a) { return isNumSort(a); }); }

    using Self = SelectedAtomicTerm;
    friend std::ostream& operator<<(std::ostream& out, Self const& self) 
    { self.apply([&](auto& x) { out << x; }); return out; }

  };

  struct SelectedAtomicTermItpAny : public NumTraitsCopro<SelectedAtomicTermItp>
  {
    using NumTraitsCopro<SelectedAtomicTermItp>::Coproduct;

    DELEGATE(clause)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)

    DELEGATE(iterSelectedSubterms)
    DELEGATE(selectedAtomicTerm)
    DELEGATE(selectedAtom)
    DELEGATE(isInequality)
    DELEGATE(sign)
    DELEGATE(termIdx)

    auto numTraits() const 
    { return applyCo([](auto& x) { return x.numTraits(); }); }

    template<class NumTraits>
    static Option<SelectedAtomicTermItpAny> from(SelectedAtomicTermItp<NumTraits> t) { return some(SelectedAtomicTermItpAny(t)); }
    static Option<SelectedAtomicTermItpAny> from(SelectedAtomicTermUF t) { return {}; }
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
    { return div(NumTraits{}, l.contextTermSum(), -l.numeral()); }

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
    using Coproduct::Coproduct;

    auto iterSelectedSubterms() const 
    { return coproductIter(applyCo([](auto x) { return x.iterSelectedSubterms(); })); }

    DELEGATE(clause)
    DELEGATE(productive)
    DELEGATE(literal)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)
    DELEGATE(selectedAtom)

   
    Option<SelectedAtomicTermItpAny> toSelectedAtomicTermItp() const
    {
      return match([](SelectedAtomicTerm t) {
          return t.apply([](auto a) { return SelectedAtomicTermItpAny::from(a); });
        },
        [](SelectedAtomicLiteral t) -> Option<SelectedAtomicTermItpAny> {
          return {};
        });
    }

    static auto iter(Clause* cl) {
      return cl->iterLits()
          .zipWithIndex() 
          .flatMap([cl](auto l_i) {
            auto l = l_i.first;
            auto i = l_i.second;
            auto nl = InequalityNormalizer::normalize(l);
            return ifElseIter(

                /* literals  t1 + t2 + ... + tn <> 0 */
                [&]() { return nl.asItp().isSome(); }, 
                [&]() { 
                  return coproductIter(nl.asItp()->applyCo([cl,i](auto itp) {
                      return itp.term().iterSummands()
                         .zipWithIndex()
                         .map([cl,i](auto s_i) -> NewSelectedAtom {
                             return  NewSelectedAtom(SelectedAtomicTerm(SelectedAtomicTermItp<decltype(itp.numTraits())>(
                                     cl, i, s_i.second
                                     )));
                         });
                  }));
                }, 
                
                /* literals  (~)t1 = t2  */
                [&]() { return nl.toLiteral()->isEquality(); },
                [&]() {
                  return iterItems(0, 1)
                     .map([cl,i](auto j) { return NewSelectedAtom(SelectedAtomicTerm(SelectedAtomicTermUF(cl, i, j))); });
                },


                /* literals  (~)P(t1 ... tn)  */
                [&]() { return iterItems(NewSelectedAtom(SelectedAtomicLiteral(cl, i))); }
            );
          });
    }
  };
#undef DELEGATE

  using SelectionCriterion = OrderingUtils::SelectionCriterion;

} // namespace Kernel
  //
// TODO optimize normalizations of sorts; we do not normalize them
 
#endif // __ALASCA_SelectionPrimitives__

