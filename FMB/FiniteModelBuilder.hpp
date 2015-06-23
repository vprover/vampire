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

  static Term* getConstant(unsigned i);

protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:
  static Array<Term*> _modelConstants;
  static unsigned created;
  static unsigned fchecked;

  void addGroundClauses();
  void addNewInstances(unsigned modelSize, bool incremental);
  void addNewFunctionalDefs(unsigned modelSize, bool incremental);
  void addNewSymmetryAxioms(unsigned modelSize);
  unsigned addNewTotalityDefs(unsigned modelSize, bool incremental);
  
  unsigned getNextSATVar();
  SATLiteral getSATLiteral(Literal* t);

  void createSolver();
  ScopedPtr<SATSolverWithAssumptions> _solver;
  unsigned _maxSatVar;
  DHMap<Literal*,unsigned> _lookup;
  DHMap<unsigned,Literal*> _revLookup;

  void addSATClause(SATClause* cl);
  SATClauseStack _clausesToBeAdded;

  // best data structure?
  ClauseList* _groundClauses;
  ClauseList* _clauses;
  ClauseList* _functionDefinitionClauses;
  Stack<Term*> _totalityFunctions;
  Stack<Term*> _constants;
  Term* _singleArityFunction;

  bool _isComplete;
  bool _incremental;
  unsigned _maxModelSize;
};

}

#endif // __FiniteModelBuilder__
