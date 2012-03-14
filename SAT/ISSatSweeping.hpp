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

  ISSatSweeping(unsigned varCnt, SATSolver& solver);
  ISSatSweeping(unsigned varCnt, SATSolver& solver, VirtualIterator<int> interestingVarIterator);


  const DHSet<Impl>& getImplications() const { return _implications; }
  const Stack<Equiv>& getEquivalences() const { return _equivStack; }
  const SATLiteralStack& getTrueLiterals() const { return _trueLits; }
private:


  bool sameCandGroup(unsigned v1, unsigned v2);


  void splitByCurrAssignment(SATLiteralStack& orig, SATLiteralStack& newGrp);
  void splitGroupsByCurrAssignment();

  void addTrueLit(SATLiteral lit);

//  void doOneLitProbing(SATLiteral lit);


  void lookForImplications(SATLiteral probedLit, bool assignedOpposite,
      bool& foundEquivalence);
  void addImplication(Impl i, bool& foundEquivalence);

  bool tryProvingImplicationInner(Impl imp, bool& foundEquivalence);
  bool tryProvingImplication(Impl imp, bool& foundEquivalence);

  void createCandidates();
  void doOneProbing();

  void run();

  unsigned _varCnt;
  Stack<unsigned> _interestingVars;

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
   * Usually, index of the largest candidate group, assigned by splitGroupsByCurrAssignment().
   *
   * In some cases it may be index of a group that is not largest, particularly when in
   * @c doOneProbing() the largest group becomes collapsed.
   */
  unsigned _biggestGroupIdx;
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

  Stack<Equiv> _equivStack;

  DHSet<unsigned> _trueVarSet;
  SATLiteralStack _trueLits;

  SATSolver& _solver;
};

}

#endif // __ISSatSweeping__
