/**
 * @file FiniteModelBuilderIncremental.hpp
 * Defines class FiniteModelBuilderIncremental.
 */

#ifndef __FiniteModelBuilderIncremental__
#define __FiniteModelBuilderIncremental__

#include "Forwards.hpp"

#include "Kernel/MainLoop.hpp"
#include "SAT/SATSolver.hpp"
#include "Lib/ScopedPtr.hpp"
#include "SortInference.hpp"

namespace FMB {
using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Shell;
using namespace SAT;

class FiniteModelBuilderIncremental : public MainLoop {
public:
  CLASS_NAME(FiniteModedlBuilder);
  USE_ALLOCATOR(FiniteModelBuilderIncremental);    
  
  FiniteModelBuilderIncremental(Problem& prb, const Options& opt);

  static Term* getConstant(unsigned i);

protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:
  static Array<Term*> _modelConstants;
  static unsigned created;
  static unsigned fchecked;

  void onModelFound(unsigned modelSize);

  void addGroundClauses();
  void addNewInstances(unsigned modelSize);
  void addNewFunctionalDefs(unsigned modelSize);
  void addNewSymmetryAxioms(unsigned modelSize,Stack<Term*>& constants, Stack<Term*>& functions);

  void addNewSymmetryAxioms(unsigned modelSize){
    if(_sortInference){
      ASS(_sortedSignature);
      for(unsigned s=0;s<_sortedSignature->sorts;s++){
        //cout << "add sorted symmetry axioms for " << s << endl;
        addNewSymmetryAxioms(modelSize,
                             _sortedSignature->sortedConstants[s],
                             _sortedSignature->sortedFunctions[s]);
      }
    }
    else{
      //cout << "add unsorted symmetry axioms" << endl;
      addNewSymmetryAxioms(modelSize,_unsortedConstants,_unsortedFunctions);
    }
  }

  unsigned addNewTotalityDefs(unsigned modelSize);
  
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
  Stack<Term*> _unsortedConstants;
  Stack<Term*> _unsortedFunctions;
  SortedSignature* _sortedSignature;

  unsigned _constantsCount;
  bool _isComplete;
  bool _sortInference;
  unsigned _maxModelSize;
};

}

#endif // __FiniteModelBuilderIncremental__
