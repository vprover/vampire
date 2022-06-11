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
 * @file Superposition.hpp
 * Defines class Superposition
 *
 */

#ifndef __IRC_Superposition__
#define __IRC_Superposition__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Shell/Options.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  Superposition(Superposition&&) = default;
  Superposition(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    , _lhs(nullptr)
    , _rhs(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif


public:
  // template<class NumTraits> static auto iterHyp1Apps(shared_ptr<IrcState>& _shared, NumTraits numTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> maxLits)
  // {
  //   return iterTraits(ownedArrayishIterator(_shared->selectedTerms<NumTraits>(premise)))
  //        .filter([maxLits](auto& maxTerm) 
  //           { return maxTerm.ircLit.symbol() == IrcPredicate::EQ; })
  //        .map([premise](auto maxTerm) 
  //           { return Hyp1<NumTraits> { .cl = premise, .pivot = maxTerm.literal, .eq = maxTerm.ircLit, .k_s1 = maxTerm.self, }; })
  //        .inspect([&](auto& hyp1) { DEBUG("hyp1 candidate: ", hyp1); });
  // }
  //
  //
  // template<class NumTraits> static auto iterHyp2Apps(shared_ptr<IrcState>& _shared, NumTraits numTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> maxLits)
  // {
  //   return iterTraits(maxLits->iterFifo())
  //         .flatMap([=](auto pivot2) { 
  //           return pvi(iterTraits(vi(new SubtermIterator(pivot2)))
  //             .filter([=](auto t) {
  //                 if (t.isTerm()) {
  //                   auto f = t.term()->functor();
  //                   return SortHelper::getResultSort(t.term()) == NumTraits::sort()
  //                       && f != NumTraits::addF()
  //                       && f != NumTraits::minusF()
  //                       && !(f == NumTraits::mulF() && NumTraits::isNumeral(*t.term()->nthArgument(0)))
  //                       && !(f == NumTraits::mulF() && NumTraits::isNumeral(*t.term()->nthArgument(1)))
  //                       && !NumTraits::isNumeral(t);
  //                 } else return false;
  //               })
  //             .map([=](auto s2) 
  //               { return Hyp2<NumTraits> { .cl = premise, .pivot = pivot2, .s2 = s2, }; }));
  //         })
  //        .inspect([&](auto& hyp2) { DEBUG("hyp2 candidate: ", hyp2); });
  // }
  // template<class NumTraits>
  // struct Hyp1 {
  //   Clause* cl;            // <- `C1 \/ ±ks1+t1 ≈ 0` 
  //   Literal* pivot;         // <-       `±ks1+t1 ≈ 0` 
  //   IrcLiteral<NumTraits> eq;// <-       `±ks1+t1 ≈ 0` 
  //   Monom<NumTraits> k_s1;   // <-       `±ks1` 
  //
  //   // The subterm to use for unification.
  //   TermList key() const { return k_s1.factors->denormalize(); }
  //
  //   static Hyp1 fromQueryResult(std::shared_ptr<IrcState> _shared, TermQueryResult res) {
  //     auto s1 = res.term; 
  //     auto eq = _shared->normalizer.renormalizeIrc<NumTraits>(res.literal).unwrap().value;
  //     return Hyp1<NumTraits> {
  //       .cl     = res.clause, // <- `C1 \/ ±ks1+t1 ≈ 0`
  //       .pivot  = res.literal, // <-       `±ks1+t1 ≈ 0`
  //       .eq     = eq,
  //       .k_s1   = eq.term().iterSummands()
  //                   .find([&](auto monom) { return monom.factors->denormalize() == s1;  })
  //                   .unwrap()
  //     };
  //   }
  //
  //   friend std::ostream& operator<<(std::ostream& out, Hyp1 const& self)
  //   { return out << *self.cl << " :: " << self.eq << " :: " << self.k_s1; }
  // };
  //
  // template<class NumTraits>
  // struct Hyp2 {
  //   Clause* cl;     // <- `C2 \/ u[s2]+t2 <> 0` 
  //   Literal* pivot; // <-       `u[s2]+t2 <> 0` 
  //   TermList s2;    // <-       `s2` 
  //
  //   // The subterm to use for unification.
  //   TermList key() const { return s2; }
  //
  //   static Hyp2 fromQueryResult(std::shared_ptr<IrcState> _shared, TermQueryResult res) {
  //
  //     return Hyp2 {
  //       .cl = res.clause,     // <- `C2 \/ u[s2]+t2 <> 0`
  //       .pivot = res.literal, // <-       `u[s2]+t2 <> 0`
  //       .s2 = res.term,
  //     };
  //   }
  //
  //   friend std::ostream& operator<<(std::ostream& out, Hyp2 const& self)
  //   { return out << *self.cl << " :: " << *self.pivot << " :: " << self.s2; }
  // };

  struct Lhs : public SelectedEquality
  {

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}


    static auto iter(IrcState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, /* literal */ SelectionCriterion::STRICTLY_MAX, 
                                           /* terms   */ SelectionCriterion::STRICTLY_MAX)
             .map([](auto x) { return Lhs(std::move(x)); });
    }
  };

  struct Rhs : public SelectedLiteral
  {
    Rhs(SelectedLiteral lit, TermList toRewrite, bool inLitPlus) 
      : SelectedLiteral(std::move(lit))
      , _toRewrite(toRewrite)
      , _inLitPlus(inLitPlus)
    {  }

    TermList _toRewrite;
    bool _inLitPlus;

    TermList toRewrite() const { return _toRewrite; }

    TermList key() const { return toRewrite(); }

    bool inLitPlus() const
    { return _inLitPlus; }

    static auto iter(IrcState& shared, Clause* cl)
    { 
      using Out = Rhs;
      return shared.selectedActivePositions(cl, 
          /* literals */ SelectionCriterion::WEAKLY_MAX, 
          /* terms    */ SelectionCriterion::STRICTLY_MAX)
        .flatMap([&](auto sel_lit) -> VirtualIterator<Out> {
           auto tup = sel_lit.match(
             [=](SelectedSummand& x) -> tuple<SelectedLiteral, TermList, bool> 
             {
                auto inLitPlus = 
                      x.isInequality() 
                        // x =  `+k s + t > 0`
                        ? x.numeral().apply([](auto n) { return n.isPositive(); })
                        // x =  `t ~ 0`
                        : x.literal()->isPositive();
                auto term = x.monom();
                return make_tuple(std::move(x), term, inLitPlus);
             },

             [](SelectedUninterpretedEquality& x) 
             {  
                auto inLitPlus = x.literal()->isPositive();
                auto term = x.biggerSide();
                return make_tuple(std::move(x), term, inLitPlus); 
             },

             [](SelectedUninterpretedPredicate& x)
             { 
                auto inLitPlus = x.literal()->isPositive();
                auto term = TermList(x.literal());
                return make_tuple(std::move(x), term, inLitPlus); 
             });

           auto sel = std::get<0>(tup);
           auto term = std::get<1>(tup);
           auto inLitPlus = std::get<2>(tup);

           if (term.isVar()) {
             return VirtualIterator<Out>::getEmpty();
           } else {
             return pvi(iterTraits(vi(new NonVariableNonTypeIterator(term.term(), /* includeSelf */ true)))
                 .map([=](TermList t) 
                   { return Rhs(sel, t, inLitPlus); }));
           }
        });
    }
      

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { 
      out << *self.literal();
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << *l;
      }
      out << "[ " << self.toRewrite() << " ] ( inLitPlus: " << self.inLitPlus() << " )";
      return out; 
    }
  };


private:


  Option<Clause*> applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      UwaResult& uwa
      ) const;



  friend class IRCSuperpositionLhsIndex;
  friend class IRCSuperpositionRhsIndex;

  shared_ptr<IrcState> _shared;
  IrcIndex<Lhs>* _lhs;
  IrcIndex<Rhs>* _rhs;
};

class InequalityTautologyDetection
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InequalityTautologyDetection);
  USE_ALLOCATOR(InequalityTautologyDetection);

  InequalityTautologyDetection(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared)) {}
  virtual ~InequalityTautologyDetection() {}

  virtual ClauseGenerationResult generateSimplify(Clause* premise) override;
private:
  // TODO make this one the same as in IRCState
  shared_ptr<IrcState> _shared;
};



#undef DEBUG
} // namespace IRC
} // namespace Inferences

#endif /*__IRC_Superposition__*/
