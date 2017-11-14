
/*
 * File TransparentSolver.hpp.
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
 * @file TransparentSolver.hpp
 * Defines class TransparentSolver.
 */

#ifndef __TransparentSolver__
#define __TransparentSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"


namespace SAT {

class TransparentSolver : public SATSolver
{
public:
  CLASS_NAME(TransparentSolver);
  USE_ALLOCATOR(TransparentSolver);
  
  TransparentSolver(SATSolver* inner);

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual void randomizeAssignment() { _inner->randomizeAssignment(); }

  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate);
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var) { return _inner->isZeroImplied(var); } //TODO: not quite sure wether this is right
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }

  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();
  virtual bool hasAssumptions() const { return _assumptions.isNonEmpty(); }

  virtual void recordSource(unsigned satlitvar, Literal* lit) { _inner->recordSource(satlitvar,lit); };
private:

  void processUnprocessed();

  void processUnit(SATClause* cl);

  void makeVarNonPure(unsigned var);

  bool tryWatchOrSubsume(SATClause* cl, unsigned forbiddenVar=0);

  bool tryToSweepPure(unsigned var, bool eager);

  void flushClausesToInner(bool onlyPropagate);

  void addInnerAssumption(SATLiteral lit, unsigned conflictCountLimit);

  struct VarInfo
  {
    VarInfo() : _unseen(true), _isRewritten(false), _unit(0), _hasAssumption(false) {}

    /** If true, _isPure needs yet to be initilized */
    bool _unseen;
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

    bool _hasAssumption;
    bool _assumedPolarity;
  };

  SATSolverSCP _inner;

  //local variables (are invalid when the execution leaves the object)
  SATClauseStack _unprocessed;
  SATClauseStack _toBeAdded;

  DArray<VarInfo> _vars;

  SATLiteralStack _assumptions;
};

}

#endif // __TransparentSolver__
