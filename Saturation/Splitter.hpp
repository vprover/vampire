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
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Shell/Options.hpp"

#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "SAT/SAT2FO.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "DP/DecisionProcedure.hpp"

#include "Lib/Allocator.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace SAT;
using namespace DP;
using namespace Indexing;

typedef Stack<SplitLevel> SplitLevelStack;

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
  void addSatClauses(const SATClauseStack& regularClauses, const SATClauseStack& conflictClauses,
                     SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  void flush(SplitLevelStack& addedComps, SplitLevelStack& removedComps);
  void getNewZeroImpliedSplits(SplitLevelStack& res);
private:
  void processDPConflicts();

  void handleSatRefutation(SATClause* ref);
  void updateSelection(unsigned satVar, SATSolver::VarAssignment asgn,
      SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  //options
  bool _eagerRemoval;
  bool _handleZeroImplied;
  Options::SplittingLiteralPolarityAdvice _literalPolarityAdvice;

  Splitter& _parent;

  SATSolverSCP _solver;
  ScopedPtr<DecisionProcedure> _dp;
  
  /**
   * Contains selected component names (splitlevels)
   */
  ArraySet _selected;
  
  /**
   * Remember variables which were zero implied before
   * to only report on the new ones.
   */
  DArray<bool> _zeroImplieds;
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
 * Let's call the SplitLevel associated with a comp its name = _compNames.get(comp)
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
    bool active;

    CLASS_NAME(Splitter::SplitRecord);
    USE_ALLOCATOR(SplitRecord);
  };
  
public:
  CLASS_NAME(Splitter);
  USE_ALLOCATOR(Splitter);

  Splitter();
  ~Splitter();

  const Options& getOptions() const;
  
  void init(SaturationAlgorithm* sa);

  bool doSplitting(Clause* cl);

  void onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement);
  void onNewClause(Clause* cl);
  void onAllProcessed();
  bool handleEmptyClause(Clause* cl);

  SATLiteral getLiteralFromName(SplitLevel compName) const;
  SplitLevel getNameFromLiteral(SATLiteral lit) const;

  bool isUsedName(SplitLevel name) const {
    CALL("Splitter::isUsedName");
    ASS_L(name,_db.size());
    return (_db[name] != 0);
  }
    
  SplitLevel splitLevelCnt() const { return _db.size(); }
  unsigned maxSatVar() const { return _sat2fo.maxSATVar(); }

  SAT2FO& satNaming() { return _sat2fo; }
private:      
  Clause* getComponentClause(SplitLevel name) const; // Martin: currently unused
  
  bool getComponents(Clause* cl, Stack<LiteralStack>& acc);
  
  SplitLevel getNameFromLiteralUnsafe(SATLiteral lit) const;

  bool shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl);
  bool handleNonSplittable(Clause* cl);
  bool tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl);

  void addComponents(const SplitLevelStack& toAdd);
  void removeComponents(const SplitLevelStack& toRemove);
  void processNewZeroImplied(const SplitLevelStack& newZeroImplied);

  void collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const;

  SplitLevel addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);
  SplitLevel addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl);

  Clause* buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig=0);

  SplitLevel tryGetComponentNameOrAddNew(const LiteralStack& comp, Clause* orig, Clause*& compCl);
  SplitLevel tryGetComponentNameOrAddNew(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);

  void recordSATClauseForAddition(SATClause* cl, bool refutation);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  bool allSplitLevelsActive(SplitSet* s);

  //settings
  Options::SplittingAddComplementary _complBehavior;
  Options::SplittingNonsplittableComponents _nonsplComps;
  unsigned _flushPeriod;
  float _flushQuotient;
  bool _congruenceClosure;
  Options::SplittingDeleteDeactivated _deleteDeactivated;

  //utility objects
  SplittingBranchSelector _branchSelector;
  ClauseVariantIndex _componentIdx;
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
  DHMap<Clause*,SplitLevel> _compNames;
  
  //state variable used for flushing:  
  /** When this number of generated clauses is reached, it will cause flush */
  unsigned _flushThreshold;
  /** true if there is a refutation to be added to the SAT solver */
  bool _haveBranchRefutation;

  /**
   * New SAT clauses to be added to the SAT solver
   *
   * We postpone adding clauses to the SAT solver to the next call of the
   * onAllProvessed() function, as at that point we may add and remove clauses
   * in the saturation algorithm (and so we'll be able to maintain the
   * correspondence between the SAT model and the clauses in the saturation).
   */
  SATClauseStack _regularClausesToBeAdded;
  SATClauseStack _conflictClausesToBeAdded;
    
  bool _fastRestart; // option's value copy
  /**
   * We are postponing to consider these clauses for a split 
   * because a conflict clause has been derived
   * and will invariably change the SAT model.
   */
  RCClauseStack _fastClauses;
  
  SaturationAlgorithm* _sa;
  
  //statistics
  unsigned _clausesSinceEmpty;
};

}

#endif // __Splitter__
