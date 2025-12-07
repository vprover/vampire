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
 * @file Splitter.hpp
 * Defines class Splitter for SAT solver-driven splitting (= AVATAR).
 */

#ifndef __Splitter__
#define __Splitter__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Shell/Options.hpp"

#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "SAT/SAT2FO.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/ProofProducingSATSolver.hpp"

#include "DP/ShortConflictMetaDP.hpp"

#include "Lib/Allocator.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace SAT;
using namespace DP;
using namespace Indexing;

typedef Stack<SplitLevel> SplitLevelStack;

struct SATClauseExtra : public InferenceExtra {
  SATClause *clause;
  SATClauseExtra(SATClause *clause) : clause(clause) {}
  void output(std::ostream &out) const override;
};

struct SplitDefinitionExtra : public InferenceExtra {
  Clause *component;
  SplitDefinitionExtra(Clause *component) : component(component) {
    component->incRefCnt();
  }
  void output(std::ostream &out) const override;
};

class Splitter;

/**
 * Object that decides which splitting components are to be selected
 */
class SplittingBranchSelector {
public:
  SplittingBranchSelector(Splitter& parent) : _parent(parent) {}
  /** To be called from Splitter::init() */
  void init();

  void updateVarCnt();
  void considerPolarityAdvice(SATLiteral lit);
  void trySetTrue(SATLiteral lit) {
    _solver.suggestPolarity(lit.var(),lit.positive());
  }

  void addSatClauseToSolver(SATClause* cl);
  void recomputeModel(SplitLevelStack& addedComps, SplitLevelStack& removedComps);
private:
  friend class Splitter;

  SAT::Status processDPConflicts();

  void handleSatRefutation();
  void updateSelection(unsigned satVar, VarAssignment asgn,
      SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  //options
  Options::SplittingLiteralPolarityAdvice _literalPolarityAdvice;

  Splitter& _parent;

  ProofProducingSATSolver _solver;
  ScopedPtr<ShortConflictMetaDP> _dp;

  /**
   * Contains selected component names (splitlevels)
   */
  ArraySet _selected;
};


/**
 * SplitLevel meanings:
 * even -- positive ground literals and non-ground components
 * odd -- negative ground literals (and possibly skolemized non-ground components -- not implemented yet)
 */
class Splitter {
private:

/**
 * ReductionRecord - records information to do with a reduction
 *
 */

  struct ReductionRecord
  {
    ReductionRecord(Clause* clause) : clause(clause),
        timestamp(clause->getReductionTimestamp()) {}
    Clause* clause;
    unsigned timestamp;
  };

/**
 *
 * SplitRecord - records the split information for the clause component
 *
 * Let's call the SplitLevel associated with a comp its "name"
 * A corresponding SplitRecord is added to _db[name]
 *
 * children - Clauses that rely on name (of comp), should be thrown away "on backtracking"
 * reduced - The clauses that have been *conditionally* reduced by this clause (and are therefore frozen)
 * active - component currently true in the model
 *
 * Comment by Giles
 */
  struct SplitRecord
  {
    SplitRecord(Clause* comp)
     : component(comp), active(false)
    {
      component->incRefCnt();
    }

    ~SplitRecord();

    void addReduced(Clause* cl);

    Clause* component;
    RCClauseStack children;
    Stack<ReductionRecord> reduced;
    Stack<PartialRedundancyEntry*> partialRedundancyEntries;
    bool active;

    // marks a component as insisting on being inserted into FO; i.e. it's only kept out if the sat solver says FALSE (regardless of eagerRemovals etc.)
    bool sticky = false;

    USE_ALLOCATOR(SplitRecord);
  };

public:
  Splitter();
  ~Splitter();

  const Options& getOptions() const;
  Ordering& getOrdering() const;

  void init(SaturationAlgorithm* sa);

  bool doSplitting(Clause* cl);

  void onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement);
  void addPartialRedundancyEntry(SplitSet* splits, PartialRedundancyEntry* e);
  void onNewClause(Clause* cl);
  void onAllProcessed();
  bool handleEmptyClause(Clause* cl);

  SplitLevel getNameFromLiteral(SATLiteral lit) const;
  Unit* getDefinitionFromName(SplitLevel compName) const;

  static std::string splitsToString(SplitSet* splits);
  static SATLiteral getLiteralFromName(SplitLevel compName);
  static std::string getFormulaStringFromName(SplitLevel compName, bool negated = false);
  static std::string getFormulaStringFromLiteral(SATLiteral l);

  bool isUsedName(SplitLevel name) const {
    ASS_L(name,_db.size());
    return (_db[name] != 0);
  }
  bool isSticky(SplitLevel name) const {
    ASS_L(name,_db.size());
    return _db[name]->sticky;
  }
  Clause* getComponentClause(SplitLevel name) const;

  SplitLevel splitLevelCnt() const { return _db.size(); }
  unsigned maxSatVar() const { return _sat2fo.maxSATVar(); }

  SAT2FO& satNaming() { return _sat2fo; }

  UnitList* preprendCurrentlyAssumedComponentClauses(UnitList* clauses);
  static bool getComponents(Clause* cl, Stack<LiteralStack>& acc, bool shuffle = false);

  /*
   * Clauses with answer literals cannot be split -- hence if we obtain a clause with
   * avatar assertions that has an answer literal, we have to un-split it.
   * This method replaces `C \/ ans(r) <- A1,...,An` with `C \/ ans(r) \/ ~A1 \/ ... \/ ~An`
   */
  Clause* reintroduceAvatarAssertions(Clause* cl);

private:
  friend class SplittingBranchSelector;

  SplitLevel getNameFromLiteralUnsafe(SATLiteral lit) const;

  bool shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl);
  bool handleNonSplittable(Clause* cl);
  bool tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl);

  void addComponents(const SplitLevelStack& toAdd);
  void removeComponents(const SplitLevelStack& toRemove);

  void collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const;

  SplitLevel addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);
  SplitLevel addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl);

  Clause* buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig=0);

  SplitLevel tryGetComponentNameOrAddNew(const LiteralStack& comp, Clause* orig, Clause*& compCl);
  SplitLevel tryGetComponentNameOrAddNew(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);

  void addSatClauseToSolver(SATClause* cl);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  bool allSplitLevelsActive(SplitSet* s);

  void conjectureSingleton(Literal* theLit, Clause* orig);

  //settings
  bool _showSplitting;

  Options::SplittingAddComplementary _complBehavior;
  Options::SplittingNonsplittableComponents _nonsplComps;
  Options::SplittingDeleteDeactivated _deleteDeactivated;
  bool _congruenceClosure;
  bool _shuffleComponents;
#if VZ3
  bool hasSMTSolver;
#endif

  //utility objects
  SplittingBranchSelector _branchSelector;
  ScopedPtr<ClauseVariantIndex> _componentIdx;
  /**
   * Registers all the sat variables and keeps track
   * of associated ground literals for those variables
   * which have one.
   */
  SAT2FO _sat2fo;
  /**
   * Information about a split level. Can be null if a split level does
   * not contain any components (e.g. for negations of non-ground
   * components)
   *
   * Invariant: if there is a clause with a level in its splitting history,
   * the _db record of this level is non-null.
   */
  Stack<SplitRecord*> _db;

  /**
   * Definitions of ground components C and ~C are shared and placed at the slot of C.
   * (So the key here is never odd!)
   **/
  DHMap<SplitLevel,Unit*> _defs;

  /** true if there was a clause added to the SAT solver since last call to onAllProcessed */
  bool _clausesAdded;

  /* as there can be both limits, it's hard to convert between them,
   * and we terminate at the earlier one, let's just keep checking both. */
  unsigned _stopSplittingAtTime; // time elapsed in milliseconds
#if VAMPIRE_PERF_EXISTS
  unsigned _stopSplittingAtInst; // mega-instructions elapsed
#endif

  bool _cleaveNonsplittables; // option's value copy

  SaturationAlgorithm* _sa;

  // clauses we already added to the SAT solver
  // not just optimisation: also prevents the SAT solver oscillating between two models in some cases
  Set<SATClause *, DerefPtrHash<DefaultHash>> _already_added;
public:
  static std::string splPrefix;

  // for observing the current model
  SplitLevel splitLevelBound() { return _db.size(); }
  bool splitLevelActive(SplitLevel lev) {
    ASS_REP(lev<_db.size(), lev);
    return (_db[lev]!=0 && _db[lev]->active);
  }
};

}

#endif // __Splitter__
