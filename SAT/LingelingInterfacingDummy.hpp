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

	LingelingInterfacing(const Shell::Options& opts, bool generateProofs=false) {}
	
	void addClause(SATClause* cl)  {}
  Status solve(unsigned conflictCountLimit)  { return UNKNOWN; }
  void ensureVarCount(unsigned newVarCnt)  {}
  unsigned newVar() override { return 0; }
  void suggestPolarity(unsigned var, unsigned pol)  {}
	VarAssignment getAssignment(unsigned var) { return NOT_KNOWN; }
	bool isZeroImplied(unsigned var) { return false; }
	void collectZeroImplied(SATLiteralStack& acc) {}
	SATClause* getZeroImpliedCertificate(unsigned var){ return 0; }
	void addAssumption(SATLiteral literal) {}
	void addCAssumption(SATClause* clause, unsigned conflictingCountLimit) {}
	void retractAllAssumptions() {}
	bool hasAssumptions() const { return false; }
	void recordSource(unsigned var, Literal* lit) {}
	Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool)  { return UNKNOWN; }
};

}//end SAT namespace

 #endif /*LingelingInterface*/
