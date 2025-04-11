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
#include "Kernel/RobSubstitution.hpp"
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
    /* return true whether this is selected in terms of bachmair-ganzinger terminology, not in terms of vampire terminology 
     * Concretely this means that for BG-selected literals no post-unification maximality checks are being performed.
     * */
    bool _bgSelected;

  public:
    __SelectedLiteral(Clause* cl, unsigned lit, bool bgSelected) : _cl(cl), _lit(lit), _bgSelected(bgSelected) {}

    Literal* literal() const { return (*_cl)[_lit]; }
    Clause* clause() const { return _cl; }
    unsigned litIdx() const { return _lit; }
    bool isBGSelected() const { return _bgSelected; }
    void setBGSelected(bool b) { _bgSelected = b; }

    static auto iter(Clause* cl, bool bgSelected) {
      return range(0, cl->size())
        .map([=](auto i) { return __SelectedLiteral(cl, i, bgSelected); });
    }

    auto allLiterals() const
    { return clause()->iterLits().cloned(); }

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
              Output::cat(_bgSelected ? "[" : " ", mainLiteral, _bgSelected ? "]" : " "),
              " \\/ ",
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
    SelectedAtomicLiteral(__SelectedLiteral sel) : __SelectedLiteral(sel) {}
    auto iterSelectedSubterms() const 
    { return termArgIterTyped(literal()) 
               .flatMap([](auto t) { return AnyAlascaTerm::normalize(t).bottomUpIter(); }); }
    Option<bool> isProductive() const { return some(literal()->isPositive()); }
    AlascaAtom selectedAtom() const { return AlascaAtom(literal()); }
    static auto iter(Ordering* ord, __SelectedLiteral const& sel) {
      return iterTraits(InequalityNormalizer::normalize(sel.literal())
        .as<AlascaLiteralUF>()
        .filter([&](auto x) { return !sel.literal()->isEquality(); })
        .map([&](auto x) { return SelectedAtomicLiteral(sel); })
        .intoIter());
    }
  };

  class SelectedAtomicTermUF 
    : public __SelectedLiteral  
  {
    bool _idx;
    using Self = SelectedAtomicTermUF;
    auto asTuple() const { return std::tie((__SelectedLiteral const&) *this, _idx); }
  public:
    SelectedAtomicTermUF(__SelectedLiteral lit, bool idx) 
      : __SelectedLiteral(std::move(lit))
      , _idx(idx) 
    { ASS(literal()->isEquality()) }

    unsigned termIdx() const { return unsigned(_idx); }

    Option<bool> isProductive() const { return some(literal()->isPositive()); }

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

  /* a literal of the shape 
   * k{1} t{1} + ... + k{n} t{n} <> 0
   * where 
   *   t{_summand} is selected
   */
  template<class NumTraits>
  class SelectedAtomicTermItp 
    : public __SelectedLiteral
  {
    unsigned _summand;
    using Self = SelectedAtomicTermItp;
    auto asTuple() const { return std::tie((__SelectedLiteral const&) *this, _summand); }
  public:

    SelectedAtomicTermItp(__SelectedLiteral lit, unsigned summand) 
      : __SelectedLiteral(std::move(lit))
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

    Option<bool> isProductive() const 
    { return isInequality() ? selectedSummand().atom().isVar() ? Option<bool>() : some(selectedSummand().numeral() > 0) 
                            : some(literal()->isPositive()); }

    // Option<bool> isProductive() const 
    // { return isInequality() ? selectedSummand().numeral() > 0 
    //                         : literal()->isPositive(); }

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

  struct MaxIterationUtil {
    template<class Self>
    static auto iter(Ordering* ord, __SelectedLiteral const& sel, OrderingUtils::SelectionCriterion selLit, OrderingUtils::SelectionCriterion selTerm) {

      auto terms = coproductIter(InequalityNormalizer::normalize(sel.literal())
        .applyCo([&](auto norm) { return Self::iterAll(sel, norm); }))
        .collectRStack();

      auto stack = OrderingUtils::maxElems(
          terms->size() ,
          [&](unsigned l, unsigned r) 
          { return ord->compare(terms[l].selectedAtomicTerm(), 
                                terms[r].selectedAtomicTerm()); },
          [&](unsigned i)
          { return terms[i].selectedAtomicTerm(); },
          selTerm)
        .map([&](auto i) 
            { return terms[i]; })
        .collectRStack();

      return arrayIter(std::move(stack));
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
    operator __SelectedLiteral const&() const { return apply([](auto& x) -> __SelectedLiteral const& { return x; }); }
#define DELEGATE(fun) \
    auto fun() const { return apply([](auto& self) { return self.fun(); }); }

#define DELEGATE_ITER(fun) \
    auto fun() const { return coproductIter(applyCo([](auto& self) { return self.fun(); })); }

    DELEGATE(clause)
    DELEGATE(isProductive)
    DELEGATE(literal)
    DELEGATE(isBGSelected)
    DELEGATE(litIdx)
    DELEGATE(termIdx)
    DELEGATE(selectedAtomicTerm)
    DELEGATE(selectedAtom)
    DELEGATE(contextLiterals)
    DELEGATE(selectedAtomicAlascaTerm)
    DELEGATE(iterSelectedSubterms)

  private:
    friend struct MaxIterationUtil;
    static auto iterAll(__SelectedLiteral const& lit, AlascaLiteralUF const& norm) {
      return ifElseIter(lit.literal()->isEquality(), 
          []() { return iterItems<bool>(0, 1); },
          []() { return iterItems<bool>(); })
        .map([=](bool b) { return SelectedAtomicTerm(SelectedAtomicTermUF(lit, b)); });
    }
    template<class NumTraits>
    static auto iterAll(__SelectedLiteral const& lit, AlascaLiteralItp<NumTraits> const& norm) {
      return range(0, norm.term().nSummands()) 
        .map([=](auto i) { return SelectedAtomicTerm(SelectedAtomicTermItp<NumTraits>(lit, i)); });
    }
  public:

    static auto iter(Ordering* ord, __SelectedLiteral const& sel, OrderingUtils::SelectionCriterion selLit, OrderingUtils::SelectionCriterion selTerm) 
    { return MaxIterationUtil::iter<SelectedAtomicTerm>(ord, sel, selLit, selTerm); }

    void setBGSelected(bool b) { return apply([&](auto& x){ return x.setBGSelected(b); }); }

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
    DELEGATE(isBGSelected)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)

    void setBGSelected(bool b) { return apply([&](auto& x){ return x.setBGSelected(b); }); }

    DELEGATE(iterSelectedSubterms)
    DELEGATE(selectedAtomicTerm)
    DELEGATE(selectedAtom)
    DELEGATE(isInequality)
    DELEGATE(sign)
    DELEGATE(termIdx)

  private:
    friend struct MaxIterationUtil;
    static auto iterAll(__SelectedLiteral const& lit, AlascaLiteralUF const& norm) 
    { return iterItems<SelectedAtomicTermItpAny>(); }

    template<class NumTraits>
    static auto iterAll(__SelectedLiteral const& lit, AlascaLiteralItp<NumTraits> const& norm) {
      return range(0, norm.term().nSummands()) 
        .map([=](auto i) { return SelectedAtomicTermItpAny(SelectedAtomicTermItp<NumTraits>(lit, i)); });
    }
  public:

    static auto iter(Ordering* ord, __SelectedLiteral const& sel, OrderingUtils::SelectionCriterion selLit, OrderingUtils::SelectionCriterion selTerm) 
    { return MaxIterationUtil::iter<SelectedAtomicTermItpAny>(ord, sel, selLit, selTerm); }



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

    static auto iter(Ordering* ord, __SelectedLiteral const& sel, OrderingUtils::SelectionCriterion selLit, OrderingUtils::SelectionCriterion selTerm) {
      return SelectedAtomicTerm::iter(ord, sel, selLit, selTerm)
        .filterMap([](auto t) { return SelectedEquality::from(t); });
    }

    bool positive() const { return literal()->isPositive(); }
    TypedTermList key() const { return biggerSide(); }
   
    TypedTermList biggerSide() const { return apply([](auto& x) { return x.selectedAtomicTerm(); }); }
    TermList smallerSide() const { return apply([](auto x) { return smallerSide(x); }); }
  };

  struct SelectedAtom : Coproduct<SelectedAtomicTerm, SelectedAtomicLiteral> {
    template<class NumTraits>
    explicit SelectedAtom(SelectedAtomicTermItp<NumTraits> self) : SelectedAtom(SelectedAtomicTerm(self)) {}
    explicit SelectedAtom(SelectedAtomicLiteral self) : Coproduct(self) {}
    explicit SelectedAtom(SelectedAtomicTerm self) : Coproduct(self) {}
    explicit SelectedAtom(SelectedAtomicTermItpAny self) : SelectedAtom(self.apply([](auto x) { return SelectedAtomicTerm(x); })) {}

    explicit SelectedAtom(SelectedEquality self) : SelectedAtom(self.apply([](auto x) { return SelectedAtomicTerm(x); })) {}

    operator __SelectedLiteral const&() const { return apply([](auto& x) -> __SelectedLiteral const& { return x; }); }

    auto iterSelectedSubterms() const 
    { return coproductIter(applyCo([](auto x) { return x.iterSelectedSubterms(); })); }

    DELEGATE(clause)
    DELEGATE(isProductive)
    DELEGATE(literal)
    DELEGATE(isBGSelected)
    DELEGATE(litIdx)
    DELEGATE(contextLiterals)
    DELEGATE(selectedAtom)

    void setBGSelected(bool b) { return apply([&](auto& x){ return x.setBGSelected(b); }); }

    Option<SelectedAtomicTermItpAny> toSelectedAtomicTermItp() const
    {
      return match([](SelectedAtomicTerm t) {
          return t.apply([](auto a) { return SelectedAtomicTermItpAny::from(a); });
        },
        [](SelectedAtomicLiteral t) -> Option<SelectedAtomicTermItpAny> {
          return {};
        });
    }

    static auto iter(Ordering* ord, __SelectedLiteral const& sel, OrderingUtils::SelectionCriterion selLit, OrderingUtils::SelectionCriterion selTerm) {
      return concatIters(
          SelectedAtomicLiteral::iter(ord, sel)
            .map([](auto x) { return SelectedAtom(x); }),
          SelectedAtomicTerm::iter(ord, sel, selLit, selTerm)
            .map([](auto x) { return SelectedAtom(x); })
          );
    }

    // TODO 2 deprecate
    static auto iter(Clause* cl, bool bgSelected) {
      return cl->iterLits()
          .zipWithIndex() 
          .flatMap([cl,bgSelected](auto l_i) {
            auto l = l_i.first;
            auto i = l_i.second;
            auto nl = InequalityNormalizer::normalize(l);
            return ifElseIter(

                /* literals  t1 + t2 + ... + tn <> 0 */
                [&]() { return nl.asItp().isSome(); }, 
                [&]() { 
                  return coproductIter(nl.asItp()->applyCo([cl,i,bgSelected](auto itp) {
                      return itp.term().iterSummands()
                         .zipWithIndex()
                         .map([cl,i,bgSelected](auto s_i) -> SelectedAtom {
                             return  SelectedAtom(SelectedAtomicTerm(SelectedAtomicTermItp<decltype(itp.numTraits())>(
                                     __SelectedLiteral(cl, i, bgSelected), s_i.second
                                     )));
                         });
                  }));
                }, 
                
                /* literals  (~)t1 = t2  */
                [&]() { return nl.toLiteral()->isEquality(); },
                [&]() {
                  return iterItems(0, 1)
                     .map([cl,i,bgSelected](auto j) { return SelectedAtom(SelectedAtomicTerm(SelectedAtomicTermUF(__SelectedLiteral(cl, i, bgSelected), j))); });
                },


                /* literals  (~)P(t1 ... tn)  */
                [&]() { return iterItems(SelectedAtom(SelectedAtomicLiteral(__SelectedLiteral(cl, i, bgSelected)))); }
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

