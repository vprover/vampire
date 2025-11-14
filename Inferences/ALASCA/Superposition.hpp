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

#ifndef __ALASCA_Inferences_Superposition__
#define __ALASCA_Inferences_Superposition__

#include "Forwards.hpp"

#include "Indexing/IndexManager.hpp"
#include "Kernel/NumTraits.hpp"
#include "BinInf.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct SuperpositionConf
{
  std::shared_ptr<AlascaState> _shared;
  // TODO make option and test and double check (?)
  bool _simultaneousSuperposition;

  SuperpositionConf(std::shared_ptr<AlascaState> shared, bool simultaneous = true) : _shared(shared), _simultaneousSuperposition(simultaneous) {  }

  static const char* name() { return "alasca superposition"; }

  struct Lhs : public SelectedEquality
  {
    static const char* name() { return "alasca superposition lhs"; }

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}


    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, /* literal */ SelectionCriterion::NOT_LEQ, 
                                           /* terms   */ SelectionCriterion::NOT_LEQ,
                                           /* include number vars */ false)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .filter([](auto& l) { return !forAnyNumTraits([&](auto n) { return n.isNumeral(l.biggerSide()); }); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }

    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_LHS_SUBST_TREE; }
  };

  struct Rhs : public SelectedLiteral
  {
    static const char* name() { return "alasca superposition rhs"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_RHS_SUBST_TREE; }

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

    static auto iter(AlascaState& shared, Clause* cl)
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
                auto term = x.selectedAtom();
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
                 // .filter([](auto& t) { return SortHelper::getResultSort(t) == IntTraits::sort() || AlascaState::globalState->isAtomic(t); })
                 .filter([](auto& t) { return AlascaState::globalState->isAtomic(t); })
                 .map([=](auto t) { return Rhs(sel, t, inLitPlus); }))
               ;
           }
        })
      .inspect([](auto& x) { ASS_REP(x.literal()->containsSubterm(x.toRewrite()), Output::cat(x, "\n", *x.literal(), "\n", x.toRewrite())); })
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
  Superposition(std::shared_ptr<AlascaState> shared, Args... args) : BinInf<SuperpositionConf>(shared, SuperpositionConf(shared, args...)) {}
};

#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_Superposition__*/
