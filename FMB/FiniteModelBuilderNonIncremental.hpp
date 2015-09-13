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

  struct GroundedTerm{
    unsigned f;
    //DArray<unsigned> grounding;
    unsigned grounding;
  };

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
  void addNewSymmetryOrderingAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms); 
  void addNewSymmetryCanonicityAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms,unsigned maxModelSize);

  void addNewSymmetryAxioms(unsigned modelSize){
      ASS(_sortedSignature);
    for(unsigned m=1;m<=modelSize;m++){
      for(unsigned s=0;s<_sortedSignature->sorts;s++){
        addNewSymmetryOrderingAxioms(m,_sortedGroundedTerms[s]);
        addNewSymmetryCanonicityAxioms(m,_sortedGroundedTerms[s],modelSize);
      }
    }
  }
  void addUseModelSize(unsigned size);

  SATLiteral getSATLiteral(unsigned func, const DArray<unsigned>& elements,bool polarity,
                           bool isFunction, unsigned modelSize);

  bool reset(unsigned modelSize);
  ScopedPtr<SATSolver> _solver;

  DHMap<unsigned,Literal*> _deletedFunctions;
  DHMap<unsigned,Unit*> _deletedPredicates;
  DArray<unsigned> del_f;
  DArray<unsigned> del_p;

  void addSATClause(SATClause* cl);
  void addSATClause(SATLiteral lit){
    static SATLiteralStack satClauseLits;
    satClauseLits.reset();
    satClauseLits.push(lit);
    addSATClause(SATClause::fromStack(satClauseLits));
  }
  SATClauseStack _clausesToBeAdded;

  ClauseList* _groundClauses;
  ClauseList* _clauses;
  SortedSignature* _sortedSignature;
  DArray<unsigned> _fminbound;
  DHMap<Clause*,DArray<unsigned>*> _clauseBounds;


  DArray<Stack<GroundedTerm>> _sortedGroundedTerms;

  DArray<unsigned> f_offsets;
  DArray<unsigned> p_offsets;

  unsigned _startModelSize; 
  bool _isComplete;
  unsigned _maxModelSize;
  unsigned _constantCount;
  bool _useConstantsAsStart;
  unsigned _maxArity;
  float _symmetryRatio;
  bool _symmetryOrderSymbols;
};

}

#endif // __FiniteModelBuilderNonIncremental__
