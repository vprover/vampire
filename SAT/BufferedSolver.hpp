/**
 * @file BufferedSolver.hpp
 * Defines class BufferedSolver.
 *
 * The idea is to buffer clauses that are true, or can be made true, by the ground model
 *
 * @author Giles
 */

#ifndef __BufferedSolver__
#define __BufferedSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"



namespace SAT {

using namespace Lib;

class BufferedSolver : public SATSolver {
public:
  BufferedSolver(SATSolver* inner);

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  virtual void randomizeAssignment() { flushUnadded(); _inner->randomizeAssignment(); }


  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false);
  virtual VarAssignment getAssignment(unsigned var);

  virtual bool isZeroImplied(unsigned var){ return _inner->isZeroImplied(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }

  virtual void ensureVarCnt(unsigned newVarCnt){ _inner->ensureVarCnt(newVarCnt);_tmaxVar=newVarCnt; }


  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();

private:

  // check if @cl is implied by current model, and record it
  // if we choose not to add it at this point
  bool checkAndRecordImplied(SATClause* cl);

  // Add any clauses that have been buffered
  void flushUnadded();


// Records whether all adds seen the last flush have been onlyPropagate
  bool _allOnlyPropagate;
  SATSolverSCP _inner;


 /**
  * A buffer for new literals that do not yet appear in the solver
  */
  DHMap<unsigned, bool> _literalBuffer;

 /**
  * A record of the assumed literals. We cannot store this in buffer as we may empty the buffer 
  * part way between an incremental SAT check
  */
  DHMap<unsigned,bool> _assumptions;

  /**
   * Clauses that have not been added to _inner as they are either implied by the assignment of _inner
   * or the variables implicitly set in _literalBuffer
   */
  SATClauseStack _unadded;

 /**
  * The maximum variable added to the SATSolver, used to detect new variables
  *
  * Obviously relies on variable numbers being increasing 
  */
  unsigned _maxVar;
  // We use a temp to track the max added since last flush
  unsigned _tmaxVar;

 /**
  * This represents the alterantive *new* SATLiterlas that could have been selected when
  * setting a SATLiteral in the _literalCache. This is used if a clause containing new literals
  * cannot be made true by the current ground assignment and _literalCache.
  *
  * TODO - implement functionality
  */
  //DHMap< unsigned, DHSet<SATLiteral> > _alternatives;

};

}

#endif // __BufferedSolver__
