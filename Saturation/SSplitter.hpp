/**
 * @file SSplitter.hpp
 * Defines class SSplitter for SAT solver-driven splitting.
 */

#ifndef __SSplitter__
#define __SSplitter__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "Splitter.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

typedef Stack<SplitLevel> SplitLevelStack;

class SSplitter;

/**
 * Object that decides which splitting components are to be selected
 *
 * Algorithm for updating component selection:
 *
 * - Put newly added clauses into SAT solver.
 * - Put newly added clauses which contain at least one positive literal into
 *   _unprocessed.
 * - If SAT solver got unsatisfiable, throw refutation.
 * - Deselect all components that were assigned false in the SAT model,
 *   empty their _watcher stacks into _unprocessed.
 * - Go through _unprocessed and:
 *   - If clause is satisfied by the selection assignment, move it to _watcher
 *   - Otherwise pick a positive literal true in the SAT model, make it selected
 *     and mode clause to its watcher. Clauses that became unsatisfied due to this
 *     should be moved to _unprocessed.
 *
 * This algorithm will terminate because inside the loop we only select additional
 * components (not deselect them) -- there can be therefore only finite number of
 * steps.
 *
 * It is guaranteed that we can always pick a positive literal true in the SAT model.
 * It is due to the fact that the SAT model satisfies all the clauses and that we never
 * select component false in the SAT model.
 *
 *
 * Selection sweep:
 *
 * We want to have as little selected components as possible. We may therefore traverse
 * through the stacks of the _watcher, and if there is a selected component whose watcher
 * is empty (or can be made empty by moving all clauses to other watchers), we can
 * deselect the component.
 */
class SSplittingBranchSelector {
public:
  SSplittingBranchSelector(SSplitter& parent) : _parent(parent) {}

  /** To be called from SSplitter::init() */
  void init();

  void ensureVarCnt(unsigned varCnt);
  void addSatClauses(const SATClauseStack& clauses, SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  void flush(SplitLevelStack& addedComps, SplitLevelStack& removedComps);
private:

  void handleSatRefutation(SATClause* ref);

  void select(SplitLevel var);
  void deselectByModel(SplitLevelStack& removedComps);
  void fixUnprocessed(SplitLevelStack& addedComps);

  bool hasAlternativeSelection(SATClause* cl, SplitLevel forbidden);

  void sweep(SplitLevelStack& addedComps, SplitLevelStack& removedComps);
  template<class It>
  void sweepVars(It varsToSweep, SplitLevelStack& sweptAway);

  bool tryAddingToWatch(SATClause* cl);

  SplitLevel getVarToSelect(SATClause* cl);

  static bool hasPositiveLiteral(SATClause* cl);

  bool isSatisfiedBySelection(SATLiteral lit);


  //options
  Options::SSplittingComponentSweeping _sweepingMode;

  SSplitter& _parent;

  unsigned _varCnt;
  SATSolverSCP _solver;

  /**
   * Clauses of which we yet need to ensure they are satisfied
   *
   * Invariant: outside of addSatClauses the stack is empty.
   */
  SATClauseStack _unprocessed;

  /**
   * Contains selected variables
   *
   * Invariant to hold outside of addSatClauses:
   * Only variables assigned true in the solver can be selected
   */
  ArraySet _selected;

  /**
   * Array of clauses kept satisfied by selecting or non-selecting
   * a particular variable
   *
   * Invariant to hold outside of addSatClauses:
   * All added clauses that contain at least one positive literal
   * are added into the wather. Each such clause occurrs here exactly
   * once.
   */
  DArray<SATClauseStack> _watcher;
};

class SSplitter : public Splitter {
private:
  struct ReductionRecord
  {
    ReductionRecord(unsigned timestamp, Clause* clause) : timestamp(timestamp), clause(clause) {}
    unsigned timestamp;
    Clause* clause;
  };

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

    CLASS_NAME("SSplitter::SplitRecord");
    USE_ALLOCATOR(SplitRecord);
  };
public:
  SSplitter();
  ~SSplitter();

  virtual void init(SaturationAlgorithm* sa);

  bool doSplitting(Clause* cl);

  void onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement);
  void onNewClause(Clause* cl);
  void onAllProcessed();
  bool handleEmptyClause(Clause* cl);

  Clause* getComponentClause(SplitLevel name);

private:
  bool handleNonSplittable(Clause* cl);
  void onNewGroundComponent(Literal* lit, Clause* nameCl, SplitLevel name);
  bool tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl);

  void addComponents(const SplitLevelStack& toAdd);
  void removeComponents(const SplitLevelStack& toRemove);

  SATLiteral getLiteralFromName(SplitLevel compName);
  void collectDependenceLits(SplitSet* splits, SATLiteralStack& acc);

  SplitLevel getComponentName(const CompRec& comp, Clause* orig, Clause*& compCl);
  SplitLevel getComponentName(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);

  SplitLevel getNewComponentName(Clause* comp);

  void addSATClause(SATClause* cl, bool refutation);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  void assertSplitLevelsActive(SplitSet* s);

  //settings
  Options::SSplittingComplementaryGround _complGroundBehavior;
  Options::SSplittingNonsplittableComponents _nonsplComps;
  unsigned _flushPeriod;
  float _flushQuotient;

  //utility objects
  SSplittingBranchSelector _branchSelector;
  ClauseVariantIndex _componentIdx;

  //state variables
  Stack<SplitRecord*> _db;
  DHMap<Clause*,SplitLevel> _compNames;
  unsigned _flushCounter;
  /** true if there is a refutation to be added to the SAT solver */
  bool _haveRefutation;

  /**
   * New SAT clauses to be added to the SAT solver
   *
   * We postpone adding clauses to the SAT solver to the next call of the
   * onAllProvessed() function, as at that point we may add and remove clauses
   * in the saturation algorithm (and so we'll be able to maintain the
   * correspondence between the SAT model and the clauses in the saturation).
   */
  SATClauseStack _clausesToBeAdded;
};

}

#endif // __SSplitter__
