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

#ifndef __LASCA_Superposition__
#define __LASCA_Superposition__

#include "Forwards.hpp"

#include "Indexing/IndexManager.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "BinInf.hpp"
#include "Shell/Options.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct SuperpositionConf
{
  std::shared_ptr<LascaState> _shared;
  // TODO make option and test and double check (?)
  bool _simultaneousSuperposition;

  SuperpositionConf(std::shared_ptr<LascaState> shared, bool simultanious = true) : _shared(shared), _simultaneousSuperposition(simultanious) {  }

  static const char* name() { return "lasca superposition"; }

  struct Lhs : public SelectedEquality
  {
    static const char* name() { return "lasca superposition lhs"; }

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}


    static auto iter(LascaState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, /* literal */ SelectionCriterion::NOT_LEQ, 
                                           /* terms   */ SelectionCriterion::NOT_LEQ,
                                           /* include number vars */ false)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .filter([](auto& l) { return !forAnyNumTraits([&](auto n) { return n.isNumeral(l.biggerSide()); }); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }

    static IndexType indexType() { return Indexing::LASCA_SUPERPOSITION_LHS_SUBST_TREE; }
  };

  struct Rhs : public SelectedLiteral
  {
    static const char* name() { return "lasca superposition rhs"; }
    static IndexType indexType() { return Indexing::LASCA_SUPERPOSITION_RHS_SUBST_TREE; }

    Rhs(SelectedLiteral lit, TypedTermList toRewrite, bool inLitPlus) 
      : SelectedLiteral(std::move(lit))
      , _toRewrite(toRewrite)
      , _inLitPlus(inLitPlus)
    {  }

    TypedTermList _toRewrite;
    bool _inLitPlus;

    TypedTermList toRewrite() const { return _toRewrite; }

    TypedTermList key() const { return toRewrite(); }
    TermList sort() const { return toRewrite().sort(); }

    bool inLitPlus() const
    { return _inLitPlus; }

    static auto iter(LascaState& shared, Clause* cl)
    { 
      using Out = Rhs;
      return shared.selectedActivePositions(cl, 
          /* literals */ SelectionCriterion::NOT_LESS, 
          /* terms    */ SelectionCriterion::NOT_LEQ,
          /* include number vars */ false)
        .flatMap([&](auto sel_lit) -> VirtualIterator<Out> {
           auto tup = sel_lit.match(
             [=](SelectedSummand& x) -> std::tuple<SelectedLiteral, TermList, bool, bool> 
             {
                auto inLitPlus = 
                      x.isInequality() 
                        // x =  `+k s + t > 0`
                        ? x.numeral().apply([](auto n) { return n.isPositive(); })
                        // x =  `t ~ 0`
                        : x.literal()->isPositive();
                auto term = x.monom();
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true);
             },

             [](SelectedUninterpretedEquality& x) 
             {  
                auto inLitPlus = x.literal()->isPositive();
                auto term = x.biggerSide();
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true); 
             },

             [](SelectedUninterpretedPredicate& x)
             { 
                auto inLitPlus = x.literal()->isPositive();
                auto term = TermList(x.literal());
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ false); 
             });

           auto sel = std::get<0>(tup);
           auto term = std::get<1>(tup);
           auto inLitPlus = std::get<2>(tup);
           auto includeSelf = std::get<3>(tup);

           if (term.isVar()) {
             return VirtualIterator<Out>::getEmpty();
           } else {
             return pvi(iterTraits(vi(new NonVariableNonTypeIterator(term.term(), includeSelf)))
                 // .filter([](auto& t) { return SortHelper::getResultSort(t) == IntTraits::sort() || LascaState::globalState->isAtomic(t); })
                 .filter([](auto& t) { return LascaState::globalState->isAtomic(t); })
                 .map([=](auto t) { return Rhs(sel, t, inLitPlus); }))
               ;
           }
        })
      .inspect([](auto& x) { ASS(x.literal()->containsSubterm(x.toRewrite())); })
      ;
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


  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(lhs,lhsVarBank, rhs, rhsVarBank, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const;
};

struct Superposition 
: public BinInf<SuperpositionConf> 
{
  template<class... Args>
  Superposition(std::shared_ptr<LascaState> shared, Args... args) : BinInf<SuperpositionConf>(shared, SuperpositionConf(shared, args...)) {}
};

class InequalityTautologyDetection
: public SimplifyingGeneratingInference
{
public:
  USE_ALLOCATOR(InequalityTautologyDetection);

  InequalityTautologyDetection(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared)) {}
  virtual ~InequalityTautologyDetection() {}

  virtual ClauseGenerationResult generateSimplify(Clause* premise) override;
private:
  std::shared_ptr<LascaState> _shared;
};



#undef DEBUG
} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_Superposition__*/
