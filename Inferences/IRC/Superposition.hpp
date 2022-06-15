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
  struct Lhs : public SelectedEquality
  {

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}


    static auto iter(IrcState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, /* literal */ SelectionCriterion::STRICTLY_MAX, 
                                           /* terms   */ SelectionCriterion::STRICTLY_MAX)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }

    TermList sort() const { ASSERTION_VIOLATION }
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
    TermList sort() const { ASSERTION_VIOLATION }

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
             [=](SelectedSummand& x) -> tuple<SelectedLiteral, TermList, bool, bool> 
             {
                auto inLitPlus = 
                      x.isInequality() 
                        // x =  `+k s + t > 0`
                        ? x.numeral().apply([](auto n) { return n.isPositive(); })
                        // x =  `t ~ 0`
                        : x.literal()->isPositive();
                auto term = x.monom();
                return make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true);
             },

             [](SelectedUninterpretedEquality& x) 
             {  
                auto inLitPlus = x.literal()->isPositive();
                auto term = x.biggerSide();
                return make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true); 
             },

             [](SelectedUninterpretedPredicate& x)
             { 
                auto inLitPlus = x.literal()->isPositive();
                auto term = TermList(x.literal());
                return make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ false); 
             });

           auto sel = std::get<0>(tup);
           auto term = std::get<1>(tup);
           auto inLitPlus = std::get<2>(tup);
           auto includeSelf = std::get<3>(tup);

           if (term.isVar()) {
             return VirtualIterator<Out>::getEmpty();
           } else {
             return pvi(iterTraits(vi(new NonVariableNonTypeIterator(term.term(), includeSelf)))
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
