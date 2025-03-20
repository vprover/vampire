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

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Indexing/IndexManager.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/NumTraits.hpp"
#include "BinInf.hpp"
#include "Lib/Reflection.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

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

  SuperpositionConf(std::shared_ptr<AlascaState> shared, bool simultanious = true) : _shared(shared), _simultaneousSuperposition(simultanious) {  }

  static const char* name() { return "alasca superposition"; }

  struct Lhs : public SelectedEquality
  {
    static const char* name() { return "alasca superposition lhs"; }

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, 
          // TODO 1.1
          // /* literal */ SelectionCriterion::NOT_LEQ, 
                                           /* terms   */ SelectionCriterion::NOT_LEQ,
                                           /* include number vars */ false)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .filter([](auto& l) { return !forAnyNumTraits([&](auto n) { return n.isNumeral(l.biggerSide()); }); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }

    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_LHS_SUBST_TREE; }
  };

  class Rhs: public NewSelectedAtom
  {
    AnyAlascaTerm _toRewrite;
  public:

    static const char* name() { return "alasca superposition rhs"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_RHS_SUBST_TREE; }

    Rhs(NewSelectedAtom self, AnyAlascaTerm toRewrite)
      : NewSelectedAtom(std::move(std::move(self)))
      , _toRewrite(toRewrite)
    {  }


    auto toRewrite() const { return _toRewrite; }

    TypedTermList key() const { return toRewrite().toTerm(); }
    // TermList sort() const { return key().sort(); }


    static auto activePositions(AlascaState& shared, Clause* cl) 
    {
      return shared.selected(cl, 
          // /* literals */ SelectionCriterion::NOT_LESS, 
          /* terms    */ SelectionCriterion::NOT_LEQ,
          /* include number vars */ false);
    }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      return activePositions(shared, cl)
        .flatMap([&](auto atom) {
            return atom.iterBottomUp()
               .filter([](AnyAlascaTerm const& t) { return t.isAtomic(); })
               .map([atom](auto t) { return Rhs(atom, t); });
        })
      .inspect([](auto& x) { ASS_REP(x.literal()->containsSubterm(x.toRewrite().toTerm()), Output::cat(x, "\n", x.literal(), "\n", x.toRewrite())); })
      ;
    }

    bool postUnificationCheck(AbstractingUnifier&, unsigned varBank) const;
    const char* postUnificationCheckName()  const
    { return "s2σ ⊴ ti ∈ active(L[s2]σ)"; }
      

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { 
      out << self.literal();
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << l;
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
