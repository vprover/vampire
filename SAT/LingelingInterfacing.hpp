/**
 * @file LingelingInterfacing.hpp
 * Defines class LingelingInterface
 */
#ifndef __LingelingInterfacing__
#define __LingelingInterfacing__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Shell/Options.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

// forward declarations
struct LGL;

namespace SAT{
  
class LingelingInterfacing : public PrimitiveProofRecordingSATSolver
{
public: 
  CLASS_NAME(LingelingInterfacing);
  USE_ALLOCATOR(LingelingInterfacing);

	//constructor for the instantiation of Lingeling
	LingelingInterfacing(const Shell::Options& opts, bool generateProofs=false);
	~LingelingInterfacing();
	
	virtual void addClause(SATClause* cl) override;

  virtual Status solve(unsigned conflictCountLimit) override;
  
  virtual void ensureVarCount(unsigned newVarCnt) override;
  virtual unsigned newVar() override;
  virtual void suggestPolarity(unsigned var, unsigned pol) override;

	/**
	* In case the status of the problem is SATISFIABLE, then return the assigned value for var
	*/
	virtual VarAssignment getAssignment(unsigned var);
	
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
	* Adds an assumption to the solver. 
	*/
	virtual void addAssumption(SATLiteral literal);
  
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

	void printLingelingStatistics();
	void printAssignment();

	//Not used in Lingeling
	virtual void recordSource(unsigned var, Literal* lit) { /* intentionally no-op */ };

	Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool) override;
  
protected:
  void solveModuloAssumptionsAndSetStatus(const SATLiteralStack& assumps, int conflictCountLimit = -1);
  
  int vampireVar2Lingeling(unsigned vvar) {
    ASS_G(vvar,0); ASS_LE(vvar,_varCnt);
    return (int)vvar;
  }
  
  static unsigned lignelingVar2Vampire(int lvar) {    
    return (unsigned)lvar;
  }
  
  int vampireLit2Lingeling(SATLiteral vlit) {
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
  /**
   * Number of variables the solver is able to handle.
   */
  unsigned _varCnt;  
  
	Status _status;
  SATLiteralStack _assumptions;
    		
	LGL * _solver;
};

}//end SAT namespace

 #endif /*LingelingInterface*/
