/**
 * @file TransparentSolver.hpp
 * Defines class TransparentSolver.
 */

#ifndef __TransparentSolver__
#define __TransparentSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/ScopedPtr.hpp"

#include "SATSolver.hpp"


namespace SAT {

class TransparentSolver : public SATSolver
{
public:
  TransparentSolver(SATSolver* inner) : _inner(inner) {}

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }

  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate);
  virtual MaybeBool getAssignment(unsigned var);

  virtual void addAssumption(SATLiteral lit, bool onlyPropagate);
  virtual void retractAllAssumptions();
  virtual bool hasAssumptions() const;
private:

  void addClause(SATClause* cl);

  bool tryWatchOrSubsume(SATClause* cl, unsigned forbiddenVar=0);

  bool trySweepPure(unsigned var);

  struct VarInfo
  {
    VarInfo() : _pureInitialized(false), _isRewritten(false), _unit(0) {}

    /** If false, _isPure needs yet to be initilized */
    bool _pureInitialized;
    bool _isPure;
    bool _isRewritten;
    /** If variable has an unit clause, it contains it, otherwise zero */
    SATClause* _unit;
    /** Relevant if _isPure. True, if there are only positive occurences
     * of the variable. */
    bool _isPurePositive;
    /** If !_isPure, must be empty */
    SATClauseStack _watched;
    /** If _isRewritter, contains literal to which the variable translates */
    SATLiteral _root;
  };

  SATSolverSCP _inner;

  SATClauseStack _toBeAdded;

  DArray<VarInfo> _vars;
};

}

#endif // __TransparentSolver__
