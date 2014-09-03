/**
 * @file LingelingInterfacing.hpp
 * Defines class LingelingInterface
 */
#ifndef __LingelingInterfacing__
#define __LingelingInterfacing__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/Exception.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "Lib/Allocator.hpp"

#include <csignal>

extern "C"{
	#include "lglib.h"
}
namespace SAT{

	using namespace Lib;
	using namespace Shell;

class LingelingInterfacing : public SATSolver
{
public: 
  CLASS_NAME(LingelingInterfacing);
  USE_ALLOCATOR(LingelingInterfacing);

	//constructor for the instantiation of Lingeling
	LingelingInterfacing(const Options& opts, bool generateProofs=false);
	~LingelingInterfacing();

	/**
	* The add clause is the incremental way for the lingeling sat solver. It is used in order to add new clause
	* to the current problem
	**/
	virtual void addClauses(SATClauseIterator clauseIterator, bool onlyPropagate=false);
	
	/**
	* return the current status of the problem
	*/
	virtual Status getStatus(){
		CALL("LingelingInterfacing::getStatus()");
		//printLingelingStatistics();
		return _status;
	}

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
	virtual bool isZeroImplied(unsigned var){ return lglfixed(_solver, var);}

	/**
	* collect all the zero-implied variables 
	* should be used only for SATISFIABLE or UNKNOWN
	*/
	virtual void collectZeroImplied(SATLiteralStack& acc){}

	/**
   	* Return a valid clause that contains the zero-implied literal
   	* and possibly the assumptions that implied it. Return 0 if @c var
   	* was an assumption itself.
   	* If called on a proof producing solver, the clause will have
   	* a proper proof history.
   	*/
	virtual SATClause* getZeroImpliedCertificate(unsigned var){ return 0;}

	/**
	* in the original solver this function took care of increasing the memory allocated for the
	* variable representation, clauses and so on.
	*/
	virtual void ensureVarCnt(unsigned newVarCnt){}

	/**
	*Adds an assumption to the solver. 
	* If conflictingCountLimit == 0 => do only unit propagation 
	* if conflictingCountLimit == UINT_MAX => do full satisfiability check
	* if the value is in between, then simply set that as the upper bound on conflictCountLimit
	*/
	virtual void addAssumption(SATLiteral literal, unsigned conflictCountLimit);
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
	virtual void recordSource(unsigned var, Literal* lit) {};

private: 
	virtual void addClausesToLingeling(SATClauseIterator iterator);
	void setSolverStatus(unsigned status);
	/** Create an inference with all the clauses that where used to derive unsat in the solver part*/
	void setRefutation();

	 enum AsgnVal {
    //the true and false value also correspond to positive
    //and negative literal polarity values
   		AS_FALSE = 0u,
    	AS_TRUE = 1u,
    	AS_UNDEFINED = 2u
  	};
	/**
	* Status of the solver 
	*/
	Status _status;
	SATClauseList * _clauseList;
	SATClause* _refutation;
	/**
	* flag which enables proof generation
	*/
	bool _generateProofs;
	bool _hasAssumptions;
	bool _unsatisfiableAssumptions;
	//keep track of the assumptions done until now
	List<SATLiteral*>* _assumptions;
	List<unsigned> *_satVariables;
	//mapping that gets used in computation of the unsat core
	DHMap<unsigned, SATClauseList* > _litToClause;
	//scoped pointer to the incremental lingleling 
	LGL * _solver;

	struct UnsatException : public Exception
  	{
    	UnsatException(SATClause* refutation=0) : refutation(refutation) {}
    	SATClause* refutation;
  	};
};

}//end SAT namespace

 #endif /*LingelingInterface*/
