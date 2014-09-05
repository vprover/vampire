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
#include "Kernel/MainLoopScheduler.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

//#include "SAT/SAT2FO.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

#include "Saturation/SaturationAlgorithmContext.hpp"

#include "DP/DecisionProcedure.hpp"

#include "Splitter.hpp"

//namespace SAT{
//class SAT2FO;
//}

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace SAT;
using namespace DP;

typedef Stack<SplitLevel> SplitLevelStack;

//class SaturationAlgorithmContext;
class SSplitter;

/**
 * Object that decides which splitting components are to be selected
 */
class SSplittingBranchSelector {
public:
  //SSplittingBranchSelector(SSplitter& parent) : _parent(parent) {}
  SSplittingBranchSelector(SAT::SAT2FO* sat2fo) : _sat2fo(sat2fo) {}

  /** To be called from SSplitter::init() */
  void init(const Options& opts);

  void updateVarCnt();
  void addSatClauses(const SATClauseStack& clauses, SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  void flush(SplitLevelStack& addedComps, SplitLevelStack& removedComps);
  void clearZeroImpliedSplits(Clause* cl);

  SplitLevel getNameFromLiteralUnsafe(SATLiteral lit) const;

private:
  SSplittingBranchSelector(const Saturation::SSplittingBranchSelector&) {}

  void processDPConflicts();

  void handleSatRefutation(SATClause* ref);
  void updateSelection(unsigned satVar, SATSolver::VarAssignment asgn,
      SplitLevelStack& addedComps, SplitLevelStack& removedComps);

  static const SSplitter* splitter() {
	  return static_cast<const SaturationAlgorithmContext*>(
			  MainLoopScheduler::context()) -> splitter();
  }

  //SATLiteral getLiteralFromName(SplitLevel compName) const;
  SplitLevel getNameFromLiteral(SATLiteral lit) const;

  //options
  bool _eagerRemoval;

  //SSplitter& _parent;
  SAT::SAT2FO* _sat2fo;

  unsigned _varCnt;
  SATSolverSCP _solver;
  ScopedPtr<DecisionProcedure> _dp;

  /**
   * Contains selected component names
   */
  ArraySet _selected;
};

/**
 * SplitLevel meanings:
 * even -- positive ground literals and non-ground components
 * odd -- negative ground literals (and possibly skolemized non-ground components -- not implemented yet)
 */
class SSplitter : public Splitter {
private:

/**
 * ReductionRecord - records information to do with a reduction
 *
 */

  struct ReductionRecord
  {
    ReductionRecord(unsigned timestamp, Clause* clause) : timestamp(timestamp), clause(clause) {}
    unsigned timestamp;
    Clause* clause;
  };

/**
 *
 * SplitRecord - records the split information for the clause component
 *
 * Note, there is a SplitLevel associated with comp, which is _compNames.get(comp)
 * A SplitRecord is added to _db[name] where name is the SAT name of comp
 *
 * children - Clauses that rely on name (of comp), should be backtracked
 * reduced - The clauses that have been *conditionally* reduced by this clause (and are therefore frozen)
 * active - true if currently frozen (maybe unfrozen, then frozen again) 
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

    CLASS_NAME(SSplitter::SplitRecord);
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

  SATLiteral getLiteralFromName(SplitLevel compName) const;
  //SplitLevel getNameFromLiteral(SATLiteral lit) const;

  bool isActiveName(SplitLevel name) const {
    CALL("SSplitter::isActiveName");
    ASS_L(name,_db.size());
    return _db[name];
  }
  Clause* getComponentClause(SplitLevel name) const;

  SplitLevel splitLevelCnt() const { return _db.size(); }
  //unsigned maxSatVar() const { return _sat2fo.maxSATVar(); }

  //SAT2FO& satNaming() { return _sat2fo; }

  void setBranchSelector(SSplittingBranchSelector* branchSelector) {
	  _branchSelector = branchSelector;
  }

  void setComponentIndex(ClauseVariantIndex* idx) {
  	  _componentIdx = idx;
  }

  void setComponentNames(DHMap<Clause*,SplitLevel>* names) {
    	  _compNames = names;
  }

  void setSAT2FO(SAT2FO* sat2fo) {
  	  _sat2fo = sat2fo;
  }

private:

  //SplitLevel getNameFromLiteralUnsafe(SATLiteral lit) const;

  bool shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl);
  bool handleNonSplittable(Clause* cl);
  bool tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause* orig, Clause*& compCl);

  void addComponents(const SplitLevelStack& toAdd);
  void removeComponents(const SplitLevelStack& toRemove);

  void collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const;

  SplitLevel addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);
  SplitLevel addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl);

  Clause* buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig=0);

  SplitLevel getComponentName(const CompRec& comp, Clause* orig, Clause*& compCl);
  SplitLevel getComponentName(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl);

//  SplitLevel getNewComponentName(Clause* comp);

  void addSATClause(SATClause* cl, bool refutation);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  void assertSplitLevelsActive(SplitSet* s);

  static bool isGround(Literal* l) { return l->ground(); }

  //settings
  Options::SSplittingAddComplementary _complBehavior;
  Options::SSplittingNonsplittableComponents _nonsplComps;
  unsigned _flushPeriod;
  float _flushQuotient;
  bool _congruenceClosure;

  //utility objects
  SSplittingBranchSelector* _branchSelector;
  ClauseVariantIndex* _componentIdx;
  SAT2FO* _sat2fo;

  //state variables
  /**
   * Information about a split level. Can be null if a split level does
   * not contain any components (e.g. for negations of non-ground
   * components)
   *
   * Invariant: if there is a clause with a level in its splitting history,
   * the _db record of this level is non-null.
   */
  Stack<SplitRecord*> _db;
  DHMap<Clause*,SplitLevel>* _compNames;
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
  SATClauseStack _clausesToBeAdded;
};

}

#endif // __SSplitter__
