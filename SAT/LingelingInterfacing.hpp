/**
 * @file LingelingInterfacing.hpp
 * Defines class LingelingInterface
 */
#ifndef __LingelingInterfacing__
#define __LingelingInterfacing__

#include "Forwards.hpp"

#include "Shell/Options.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "Lib/Allocator.hpp"
#include <csignal>

typedef struct LGL LGL;

namespace SAT{
  
class LingelingInterfacing : public SATSolver
{
public: 
  CLASS_NAME(LingelingInterfacing);
  USE_ALLOCATOR(LingelingInterfacing);

	//constructor for the instantiation of Lingeling
	LingelingInterfacing(const Shell::Options& opts, bool generateProofs=false);
	~LingelingInterfacing();

	/**
	* The add clause is the incremental way for the lingeling sat solver. It is used in order to add new clause
	* to the current problem
	**/
	virtual void addClauses(SATClauseIterator clauseIterator, bool onlyPropagate,bool useInPartialModel);
	
	/**
	* return the current status of the problem
	*/
	virtual Status getStatus(){
		CALL("LingelingInterfacing::getStatus()");		
		return _status;
	}

  virtual void ensureVarCnt(unsigned newVarCnt);
  
	/**
	* In case the status of the problem is SATISFIABLE, then return the assigned value for var
	*/
	virtual VarAssignment getAssignment(unsigned var);

	/**
	* Try to find another assignment which is likely to be different from the current one. 
	* 
	* as a precondition, the solver must have SATISFIABLE status
	*/
	virtual void randomizeAssignment();
	
	/**
	* In case the solver has status SATISFIABLE and the assignment of @c var was done at level 1, 
	* return 1.  
	* 
	*/
	virtual bool isZeroImplied(unsigned var);
  
	/**
	* collect all the zero-implied variables 
	* should be used only for SATISFIABLE or UNKNOWN
	*/
	virtual void collectZeroImplied(SATLiteralStack& acc);

	/**
   	* Return a valid clause that contains the zero-implied literal
   	* and possibly the assumptions that implied it. Return 0 if @c var
   	* was an assumption itself.
   	* If called on a proof producing solver, the clause will have
   	* a proper proof history.
   	*/
	virtual SATClause* getZeroImpliedCertificate(unsigned var){ return 0; }
	
	/**
	*Adds an assumption to the solver. 
	* If conflictingCountLimit == 0 => do only unit propagation 
	* if conflictingCountLimit == UINT_MAX => do full satisfiability check
	* if the value is in between, then simply set that as the upper bound on conflictCountLimit
	*/
	virtual void addAssumption(SATLiteral literal, unsigned conflictCountLimit);
  
  //since lingeling allows assumption of clauses, let's have a function which does that
	void addCAssumption(SATClause* clause, unsigned conflictingCountLimit);
  
	/**
	* Retracts all the assumption made until now.
	*/
	virtual void retractAllAssumptions();

	/**
	* check if there is at least one assumption made until now
	*/
	virtual bool hasAssumptions() const;

	/**
	* get the refutation
	*/
	virtual SATClause* getRefutation();

	void printLingelingStatistics();
	void printAssignment();

	//Not used in Lingeling
	virtual void recordSource(unsigned var, Literal* lit) { /* intentionally no-op */ };

protected:
  void solveModuloAssumptionsAndSetStatus(int conflictCountLimit = -1);
  
  static int vampireVar2Lingeling(unsigned vvar) {
    ASS_G(vvar,0);
    return (int)vvar;
  }
  
  static unsigned lignelingVar2Vampire(int lvar) {    
    return (unsigned)lvar;
  }
  
  static int vampireLit2Lingeling(SATLiteral vlit) {
    int lit = vampireVar2Lingeling(vlit.var());
    if (vlit.isNegative()) {
      return -lit;
    } else {
      return lit;
    }
  }
  
  static const SATLiteral lingelingLit2Vampire(int llit) {
    ASS_NEQ(llit,0);
    return SATLiteral(lignelingVar2Vampire(abs(llit)),llit > 0);
  }
  
private:
	Status _status;
  SATLiteralStack _assumptions;  
  SATClauseList* _addedClauses; 
  		
	LGL * _solver;
};

}//end SAT namespace

 #endif /*LingelingInterface*/
