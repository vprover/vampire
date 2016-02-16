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
#include "Lib/Deque.hpp"

namespace FMB {
using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Shell;
using namespace SAT;

  /**
   * A GroundedTerm represents function f grounded with an array of ground constants 
   * Previously a single ground constant was used; but this did not work in the multi-sorted case
   * These are used to order grounded terms for symmetry breaking
   */
  struct GroundedTerm{
    unsigned f;
    DArray<unsigned> grounding;

    vstring toString(){
      vstring ret = Lib::Int::toString(f)+"[";
      for(unsigned i=0;i<grounding.size();i++){
        if(i>0) ret +=",";
        ret+=Lib::Int::toString(grounding[i]);
      }
      return ret+"]";
    }

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
  void onModelFound();

  // Adds constraints from ground clauses (same constraints for each model size)
  // A clause will only be ground if it contains (dis)equalities between constants, so very few of these!
  void addGroundClauses();
  // Adds constraints from grounding the non-ground clauses
  void addNewInstances();

  // uses _distinctSortSizes to estimate how many instances would we generate
  unsigned estimateInstanceCount();

  // Add constraints from functionality of function symbols in signature (except those removed in preprocessing)
  void addNewFunctionalDefs();

  unsigned estimateFunctionalDefCount();

  // Add constraints from totality of function symbols in signature (except those removed in preprocessing)
  void addNewTotalityDefs();

  // Add constraints for symmetry ordering i.e. the first modelSize groundedTerms are ordered
  void addNewSymmetryOrderingAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms); 
  // Add constraints for canonicity of symmetry order i.e. if a groundedTerm uses a constant smaller terms use smaller constants
  void addNewSymmetryCanonicityAxioms(unsigned modelSize,Stack<GroundedTerm>& groundedTerms,unsigned maxModelSize);

  // Add all symmetry constraints
  // For each model size up to the maximum add both ordering and canonicity constraints for each (inferred) sort
  void addNewSymmetryAxioms(){
      ASS(_sortedSignature);
    
    for(unsigned s=0;s<_sortedSignature->sorts;s++){
      //cout << "SORT " << s << endl;
      unsigned modelSize = _sortModelSizes[s];
      for(unsigned m=1;m<=modelSize;m++){
        //cout << "MSIZE " << m << endl;
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
                           bool isFunction);

  // resets all structures and SAT solver using _sortModelSizes 
  bool reset();

  // make the symmetry orderings
  void createSymmetryOrdering();
  // The per-sort ordering of grounded terms used for symmetry breaking
  DArray<Stack<GroundedTerm>> _sortedGroundedTerms;

  // SAT solver used to solve constraints (a new one is used for each model size)
  ScopedPtr<SATSolverWithAssumptions> _solver;

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
  // Record for each clause the sorts of the variables 
  // As clauses are normalized variables will be numbered 0,1,...
  DHMap<Clause*,DArray<unsigned>*> _clauseVariableSorts;

  // There is a implicit mapping from ground terms to SAT variables
  // These offsets give the SAT variable for the *first* grounding of each function or predicate symbol
  // Then the SAT variables for other groundings can be computed from this
  DArray<unsigned> f_offsets;
  DArray<unsigned> p_offsets;

  /* Each distinctSort has as many markers as is its current size.
   * Their offsets are stored on per sort basis.
   */
  DArray<unsigned> marker_offsets;

  /**
   * use marker_offsets to figure out to which sort does a variable belong
   */
  unsigned which_sort(unsigned var) {
    ASS_GE(var,marker_offsets[0]);
    unsigned j;
    for (j = 0; j < _distinctSortSizes.size()-1; j++) {
      if (var < marker_offsets[j+1]) {
        return j;
      }
    }
    ASS_EQ(j,_distinctSortSizes.size()-1);
    ASS_GE(var,_distinctSortSizes[j]);
    return j;
  }

  /** Parameters to the FBM saturation **/

  // Currently an experimental option allows you to start at larger model sizes
  // TODO in the future we could use this for a cheap way to 'pause' and 'restart' fmb
  unsigned _startModelSize; 
  // If we detect incompleteness at init then we terminate immediately at runImpl
  bool _isComplete;
  // Option used in symmetry breaking
  float _symmetryRatio;

  // sizes to use for each sort
  DArray<unsigned> _sortModelSizes;
  DArray<unsigned> _distinctSortSizes;

  // the sort constraints from injectivity/surjectivity
  // pairs of distinct sorts where pair.first >= pair.second
  Stack<std::pair<unsigned,unsigned>> _distinct_sort_constraints;
  // pairs of distinct sorts where pair.first > pair.second
  Stack<std::pair<unsigned,unsigned>> _strict_distinct_sort_constraints;

  // returns false one failure
  bool increaseModelSizes();

  // Record the number of constants in the problem per distinct sort
  DArray<unsigned> _distinctSortConstantCount;
  // min and max sizes for distinct sorts
  DArray<unsigned> _distinctSortMins;
  DArray<unsigned> _distinctSortMaxs;
  //unsigned _maxModelSizeAllSorts;
};
}

#endif // __FiniteModelBuilder__
