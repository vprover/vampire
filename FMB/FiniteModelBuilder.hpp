/**
 * @file FiniteModelBuilder.hpp
 * Defines class FiniteModelBuilder.
 */

#ifndef __FiniteModelBuilder__
#define __FiniteModelBuilder__

#include "Forwards.hpp"

#include "Kernel/MainLoop.hpp"
#include "SAT/SATSolver.hpp"
#include "Lib/ScopedPtr.hpp"

namespace FMB {
using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Shell;
using namespace SAT;

class FiniteModelBuilder : public MainLoop {
public:
  CLASS_NAME(FiniteModedlBuilder);
  USE_ALLOCATOR(FiniteModelBuilder);    
  
  FiniteModelBuilder(Problem& prb, const Options& opt);


protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:

  void addNewInstances(unsigned modelSize);
  void addNewFunctionalDefs(unsigned modelSize);
  unsigned addNewTotalityDefs(unsigned modelSize);
  
  unsigned getNextSATVar();
  SATLiteral getSATLiteral(Literal* t);

  ScopedPtr<SATSolverWithAssumptions> _solver;
  unsigned _maxSatVar;
  DHMap<Literal*,unsigned> _lookup;

  void addSATClause(SATClause* cl);
  SATClauseStack _clausesToBeAdded;

  // best data structure?
  ClauseList* _clauses;
  ClauseList* _functionDefinitionClauses;
  Stack<Term*> _totalityFunctions;
};

}

#endif // __FiniteModelBuilder__
