/**
 * @file FiniteModelBuilderNonIncremental.hpp
 * Defines class FiniteModelBuilderNonIncremental.
 */

#ifndef __FiniteModelBuilderNonIncremental__
#define __FiniteModelBuilderNonIncremental__

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

class FiniteModelBuilderNonIncremental : public MainLoop {
public:
  CLASS_NAME(FiniteModedlBuilder);
  USE_ALLOCATOR(FiniteModelBuilderNonIncremental);    
  
  FiniteModelBuilderNonIncremental(Problem& prb, const Options& opt);

  static Term* getConstant(unsigned i);

protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:

  void onModelFound(unsigned modelSize);

  void addGroundClauses();
  void addNewInstances(unsigned modelSize);
  void addNewFunctionalDefs(unsigned modelSize);
  void addNewTotalityDefs(unsigned modelSize);
  void addNewSymmetryAxioms(unsigned modelSize,Stack<Term*>& constants, Stack<Term*>& functions);

  void addNewSymmetryAxioms(unsigned modelSize){
      ASS(_sortedSignature);
      for(unsigned s=0;s<_sortedSignature->sorts;s++){
        addNewSymmetryAxioms(modelSize,
                             _sortedSignature->sortedConstants[s],
                             _sortedSignature->sortedFunctions[s]);
      }
  }

  SATLiteral getSATLiteral(unsigned func, DArray<unsigned> elements,bool polarity, 
                           bool isFunction, unsigned modelSize);

  void reset(unsigned modelSize);
  ScopedPtr<SATSolver> _solver;

  void addSATClause(SATClause* cl);
  SATClauseStack _clausesToBeAdded;

  ClauseList* _groundClauses;
  ClauseList* _clauses;
  SortedSignature* _sortedSignature;
  DArray<unsigned> _fminbound;
  DHMap<Clause*,DArray<unsigned>*> _clauseBounds;

  DArray<unsigned> f_offsets;
  DArray<unsigned> p_offsets;

  bool _isComplete;
  unsigned _maxModelSize;
};

}

#endif // __FiniteModelBuilderNonIncremental__
