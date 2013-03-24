/**
 * @file Solver.hpp
 * Defines class Solver.
 */

#ifndef __Solver__
#define __Solver__
#if GNUMP

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Event.hpp"
#include "Lib/ScopedPtr.hpp"

#include "AssignmentSelector.hpp"
#include "BoundsArray.hpp"
#include "BoundPropagator.hpp"
#include "DecisionStack.hpp"
#include "VariableSelector.hpp"

namespace Solving {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class Solver {
public:
  class NumberImprecisionException {
  public:
    NumberImprecisionException() {

    }};

  Solver(size_t varCnt, Options& opt, Statistics & stats);
  ~Solver();
  void load(ConstraintRCList* constraints);
  void solve();

  size_t varCnt() const { return _varCnt; }
  DecisionLevel getDepth() const { return _decStack.depth(); }

  BoundsArray& getBounds() { return _bounds; }
  Statistics& getStats() { return _stats; }

  bool isProblemVar(Var v) const { return _problemVariables[v]; }

  ConstraintList* inputConstraints() const { return _inputConstraints; }
  ConstraintList* aliveConstraints() const { return _aliveConstraints; }

  void retainConstraint(Constraint* constr);

  typedef TwoParamEvent<Var,Constraint*> ConflictEvent;

  ConflictEvent onConflict;

private:

  class RefutationFoundException;

  void collectInputBounds();
  bool haveFullAssignment();
  void makeDecisionPoint(Var v, const BoundNumber& val);
  void handleConflicts();
  void backtrack(DecisionLevel lev);

  DecisionLevel getHighestDecisionLevel(Constraint& conflictCollapsingConstraint);

  void setForcedDecision(Var v);
  bool tryUseForcedDecision(Var& v);

  Statistics& _stats;

  size_t _varCnt;

  BoundsArray _bounds;
  DecisionStack _decStack;

  ScopedPtr<VariableSelector> _varSelector;
  ScopedPtr<AssignmentSelector> _asgSelector;
  ScopedPtr<BoundPropagator> _propagator;

  /** Variables that occur in the problem have @c true at their index */
  DArray<bool> _problemVariables;

  ConstraintList* _inputConstraints;
  ConstraintRCList* _inputConstraintsRC;

  /** Input constraints with at least two variables */
  ConstraintList* _aliveConstraints;
  ConstraintRCList* _aliveConstraintsRC; //holds references to alive constraints

  bool _haveForcedDecision;
  Var _forcedDecisionVar;

  //no copying
  Solver(const Solver&);
  Solver& operator=(const Solver&);
};

}
#endif //GNUMP
#endif // __Solver__
