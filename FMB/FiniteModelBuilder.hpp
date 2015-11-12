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
#include "SortInference.hpp"

namespace FMB {
using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Shell;
using namespace SAT;

  /**
   * A GroundedTerm represents function f grounded with domain constant 'grounding' 
   * Currently a single constant is used i.e. we get f(1,1,1) for f of arity 3
   * These are used to order grounded terms for symmetry breaking
   */
  struct GroundedTerm{
    unsigned f;
    //DArray<unsigned> grounding;
    unsigned grounding;
  };

class FiniteModelBuilder : public MainLoop {
public:
  CLASS_NAME(FiniteModedlBuilder);
  USE_ALLOCATOR(FiniteModelBuilder);    
  
  FiniteModelBuilder(Problem& prb, const Options& opt);

protected:
  // Sets up everything
  virtual void init();

  // Runs the saturation loop
  virtual MainLoopResult runImpl();

private:

  // Creates the model output
  void onModelFound(unsigned modelSize);

  // Adds constraints from ground clauses (same constraints for each model size)
  // A clause will only be ground if it contains (dis)equalities between constants, so very few of these!
  void addGroundClauses();
  // Adds constraints from grounding the non-ground clauses
  void addNewInstances(unsigned modelSize);
  // Add constraints from functionality of function symbols in signature (except those removed in preprocessing)
  void addNewFunctionalDefs(unsigned modelSize);
  // Add constraints from totality of function symbols in signature (except those removed in preprocessing)
  void addNewTotalityDefs(unsigned modelSize);

  // Add constraints for symmetry ordering i.e. the first modelSize groundedTerms are ordered
  void addNewSymmetryOrderingAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms); 
  // Add constraints for canonicity of symmetry order i.e. if a groundedTerm uses a constant smaller terms use smaller constants
  void addNewSymmetryCanonicityAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms,unsigned maxModelSize);

  // Add all symmetry constraints
  // For each model size up to the maximum add both ordering and canonicity constraints for each (inferred) sort
  void addNewSymmetryAxioms(unsigned modelSize){
      ASS(_sortedSignature);
    for(unsigned m=1;m<=modelSize;m++){
      for(unsigned s=0;s<_sortedSignature->sorts;s++){
        addNewSymmetryOrderingAxioms(m,_sortedGroundedTerms[s]);
        addNewSymmetryCanonicityAxioms(m,_sortedGroundedTerms[s],modelSize);
      }
    }
  }
  // Add the constraint that some term is allocated to the model size
  // Based on the assumption that all previous model sizes have been shown to be insufficient
  void addUseModelSize(unsigned size);

  // Converts a grounded term (literal) into a SATLiteral
  // The elements are the domain constants to use as parameters
  // polarity is used if isFunction is false
  SATLiteral getSATLiteral(unsigned func, const DArray<unsigned>& elements,bool polarity,
                           bool isFunction, unsigned modelSize);

  // resets all structures and SAT solver using the given modelSize
  bool reset(unsigned modelSize);

  // make the symmetry orderings
  void createSymmetryOrdering(unsigned modelSize);
  // The per-sort ordering of grounded terms used for symmetry breaking
  DArray<Stack<GroundedTerm>> _sortedGroundedTerms;

  // SAT solver used to solve constraints (a new one is used for each model size)
  ScopedPtr<SATSolver> _solver;

  // Structures to record symbols removed during preprocessing i.e. via definition elimination
  // These are ignored throughout finite model building and then the definitions (recorded here)
  // are used to give the interpretation of the function/predicate if a model is found
  DHMap<unsigned,Literal*> _deletedFunctions;
  DHMap<unsigned,Unit*> _deletedPredicates;
  DHMap<unsigned,Unit*> _partiallyDeletedPredicates; 
  DHMap<unsigned,bool> _trivialPredicates;
  // if del_f[i] (resp del_p[i]) is true then that function (resp predicate) should be ignored
  DArray<unsigned> del_f;
  DArray<unsigned> del_p;

  // Add a SATClause to the SAT solver
  void addSATClause(SATClause* cl);
  // Add a singleton SATClause in the form of a SATLiteral to the SAT solver
  void addSATClause(SATLiteral lit){
    static SATLiteralStack satClauseLits;
    satClauseLits.reset();
    satClauseLits.push(lit);
    addSATClause(SATClause::fromStack(satClauseLits));
  }
  // SAT clauses to be added. We record them so we can delete them after calling the SAT solver
  SATClauseStack _clausesToBeAdded;

  // The inferred signature of sorts (see SortInference.hpp)
  SortedSignature* _sortedSignature;
  // clauses of the problem after preprocessing
  ClauseList* _groundClauses;
  ClauseList* _clauses;

  // Record for function symbol the minimum bound of the return sort or any parameter sorts 
  DArray<unsigned> _fminbound;
  // Record for each clause the minimum bounds for argument sorts of each literal
  //  if the literal is equality then this takes the min of each argument
  // This assumes that clauses are not reordered (only happens when we do selection, which we do not)
  DHMap<Clause*,DArray<unsigned>*> _clauseBounds;

  // The per-sort ordering of grounded terms used for symmetry breaking
  DArray<Stack<GroundedTerm>> _sortedGroundedTerms;

  // There is a implicit mapping from ground terms to SAT variables
  // These offsets give the SAT variable for the *first* grounding of each function or predicate symbol
  // Then the SAT variables for other groundings can be computed from this
  DArray<unsigned> f_offsets;
  DArray<unsigned> p_offsets;

  /** Parameters to the FBM saturation **/

  // Currently an experimental option allows you to start at larger model sizes
  unsigned _startModelSize; 
  // If we detect incompleteness at init then we terminate immediately at runImpl
  bool _isComplete;
  // Record the maximum model size if there is one
  unsigned _maxModelSize;
  // Record the number of constants in the problem
  unsigned _constantCount;
  // An experimental option that uses the number of constants in the problem as the initial model size
  // This is incomplete and I can't remember why I tried it
  bool _useConstantsAsStart;
  // The maximum arity, used to detect if we have at most 0,1 or >1 arity functions
  unsigned _maxArity;
  // Option used in symmetry breaking
  float _symmetryRatio;
};

}

#endif // __FiniteModelBuilder__
