
/*
 * File ISSatSweeping.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ISSatSweeping.hpp
 * Defines class ISSatSweeping.
 */

#ifndef __ISSatSweeping__
#define __ISSatSweeping__

#include "Forwards.hpp"

#include "Lib/ArrayMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class ISSatSweeping
{
public:
  /**
   * Represents implication "first --> second".
   */
  typedef pair<SATLiteral,SATLiteral> Impl;
  typedef pair<SATLiteral,SATLiteral> Equiv;

  ISSatSweeping(unsigned varCnt, SATSolverWithAssumptions& solver,
      IntIterator interestingVarIterator = IntIterator::getInvalid(),
      bool doRandomSimulation = true, unsigned conflictLimit = UINT_MAX, bool collectImplications=true);


  const DHSet<Impl>& getImplications() const { return _implications; }
  const Stack<Equiv>& getEquivalences() const { return _equivStack; }
  const SATLiteralStack& getTrueLiterals() const { return _trueLits; }

  SATLiteral getCandidateLiteral(unsigned var) const { return SATLiteral(var, _candidateVarPolarities[var]); }
  /**
   * Return union-find structure with equivalence classes.
   *
   * As an artifact of the IntUnionFind object, there is also a class for
   * "variable" 0 which should be ignored, as SAT variables start from 1.
   */
  const IntUnionFind& getEquivalenceClasses() const { return _equivalentVars; }
private:


  bool sameCandGroup(unsigned v1, unsigned v2);


  void splitByCurrAssignment(SATLiteralStack& orig, SATLiteralStack& newGrp);
  void splitGroupsByCurrAssignment();

  void addTrueLit(SATLiteral lit);

//  void doOneLitProbing(SATLiteral lit);


  void lookForImplications(SATLiteral probedLit, bool assignedOpposite,
      bool& foundEquivalence);
  void addImplication(Impl i, bool& foundEquivalence);
  void onRedundantImplicationDiscovered();
  void doRedundantImplicationSweeping();

  bool tryProvingImplicationInner(Impl imp, bool& foundEquivalence);
  bool tryProvingImplication(Impl imp, bool& foundEquivalence);

  void createCandidates();
  void tryRandomSimulation();

  bool getProbingCandidatesFromGroup(SATLiteralStack& grp, unsigned firstIndex, SATLiteral& cand1, SATLiteral& cand2);
  bool getProbingCandidatesWithinRotation(SATLiteral& cand1, SATLiteral& cand2);
  bool nextRotation();
  bool getProbingCandidates(SATLiteral& cand1, SATLiteral& cand2);

  bool doOneProbing();

  void run();

  //options
  bool _doRandomSimulation;
  bool _conflictUpperLimit;
  bool _collectImplications;


  unsigned _varCnt;
  Stack<unsigned> _interestingVars;
  ArraySet _interestingVarsSet;

  /**
   * Together with _probingElementIndex serve to ensure fair rotation of
   * probing candidates. Contain index of a group and _probingElementIndex
   * of element that is to be probed next (with a successive element of a
   * group as the second implication candidate).
   *
   * The probing element selection should be fair on average, sometimes an
   * element can be skipped from a round as the groups in the group stack
   * may change order from time to time.
   */
  unsigned _probingGroupIndex;
  unsigned _probingElementIndex;

  /**
   * Limit on the number of conflicts during probing. Is increased by the
   * @c getProbingCandidates function when a rotation is finished.
   */
  unsigned _conflictCountLimit;

  /**
   * If _conflictUpperLimit is set to less than UINT_MAX, will be set to true
   * when the _conflictCountLimit goes over the upper limit value. This will
   * terminate the probing in the run() function.
   */
  bool _reachedUpperConflictLimit;

  /**
   * Polarities of candidate literals.
   * Invariant: there is a satisfying assignment with candidate literals set to true
   * Consequence: If there is an equivalence between two variables, it will be between
   * 	their candidate literals (there cannot be equivalence between cand. literal and
   * 	negation of the other cand. literal).
   */
  DArray<bool> _candidateVarPolarities;
  /**
   * Invariant: size of each candidate group is at least two.
   * Invariant: none of literals in the candidate groups is 0-implied to be false.
   */
  Stack<SATLiteralStack> _candidateGroups;

  /**
   * A measure of progress, if it decreases, it means we have discovered some new facts.
   *
   * Is computed as the number of literals in candidate groups minus the number of
   * candidate groups. It is updated in @c splitGroupsByCurrAssignment().
   */
  unsigned _unfinishedAmount;

  /**
   * Candidate group indexes of variables. Populated by splitGroupsByCurrAssignment().
   */
  ArrayMap<unsigned> _candidateGroupIndexes;

  IntUnionFind _equivalentVars;

  /**
   * Discovered implications (some discovered equivalences might not be included)
   *
   * Invariant: at least one of the literals is a candidate literal. The second may be also
   * 	a negation of a candidate literal.
   */
  DHSet<Impl> _implications;

  /**
   * Used for scheduling calls to doRedundantImplicationSweeping() in
   * onRedundantImplicationDiscovered().
   */
  size_t _lastSweepingImplicationCnt;

  Stack<Equiv> _equivStack;

  DHSet<unsigned> _trueVarSet;
  SATLiteralStack _trueLits;

  SATSolverWithAssumptions& _solver;
};

}

#endif // __ISSatSweeping__
