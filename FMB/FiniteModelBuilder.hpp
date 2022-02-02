/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FiniteModelBuilder.hpp
 * Defines class FiniteModelBuilder.
 */

#ifndef __FiniteModelBuilder__
#define __FiniteModelBuilder__

#include "Forwards.hpp"

#if VZ3
#include "z3++.h"
#include "z3_api.h"
#endif

#include "Kernel/MainLoop.hpp"
#include "SAT/SATSolver.hpp"
#include "Lib/ScopedPtr.hpp"
#include "SortInference.hpp"
#include "Lib/BinaryHeap.hpp"

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
  ~FiniteModelBuilder();

protected:
  // Sets up everything
  virtual void init();

  // Runs the saturation loop
  virtual MainLoopResult runImpl();

private:

  // Creates the model output
  void onModelFound();

  // Adds constraints from ground clauses (same constraints for each model size)
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

  // do contour encoding instead of point-wise
  bool _xmass;

  // if (_xmass) {

  /* Each distinctSort has as many markers as is its current size.
   * Their offsets are stored on per sort basis.
   */
  DArray<unsigned> marker_offsets;

  // } else {

  /* for each distinctSort i there is a variable (totalityMarker_offset+i)
   * which we use in the encoding to learn which domain should grow in order to possibly resolve a conflict.
   */
  unsigned totalityMarker_offset;
  /* for each distinctSort i there is a variable (instancesMarker_offset+i)
   * which we use in the encoding to learn whether it makes sense to change the domain sizes at all.
   */
  unsigned instancesMarker_offset;

  // }

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
  // If we detect that FMB is not an approprate sa at init we then terminate immediately at runImpl
  bool _isAppropriate;
  // Option used in symmetry breaking
  float _symmetryRatio;

  // how often do we pick the next domain to grow by size and how often by weight (= encoding size estimate)
  unsigned _sizeWeightRatio;

  // sizes to use for each sort
  DArray<unsigned> _sortModelSizes;
  DArray<unsigned> _distinctSortSizes;

  enum ConstraintSign {
    EQ,     // the value has to matched
    LEQ,    // the value needs to be less or equal
    GEQ,    // the value needs to be greater or equal
    STAR    // we don't care about this value
  };

  typedef DArray<pair<ConstraintSign,unsigned>> Constraint_Generator_Vals;

  class DSAEnumerator { // Domain Size Assignment Enumerator - for the point-wise encoding case
  public:
    virtual bool init(unsigned, DArray<unsigned>&, Stack<std::pair<unsigned,unsigned>>&, Stack<std::pair<unsigned,unsigned>>&) { return true; }
    virtual void learnNogood(Constraint_Generator_Vals& nogood, unsigned weight) = 0;
    virtual bool increaseModelSizes(DArray<unsigned>& newSortSizes, DArray<unsigned>& sortMaxes) = 0;
    virtual bool isFmbComplete(unsigned noDomains) { return false; }
    virtual ~DSAEnumerator() {}
  };

  DSAEnumerator* _dsaEnumerator;

  class HackyDSAE : public DSAEnumerator {
    struct Constraint_Generator {
      CLASS_NAME(FiniteModedlBuilder::HackyDSAE::Constraint_Generator);
      USE_ALLOCATOR(FiniteModelBuilder::HackyDSAE::Constraint_Generator);

      Constraint_Generator_Vals _vals;
      unsigned _weight;

      Constraint_Generator(unsigned size, unsigned weight)
        : _vals(size), _weight(weight) {}
      Constraint_Generator(Constraint_Generator_Vals& vals, unsigned weight)
        : _vals(vals), _weight(weight) {}
    };

    struct Constraint_Generator_Compare {
      static Comparison compare (Constraint_Generator* c1, Constraint_Generator* c2)
      { return c1->_weight < c2->_weight ? LESS : c1->_weight == c2->_weight ? EQUAL : GREATER; }
    };

    typedef Lib::BinaryHeap<Constraint_Generator*,Constraint_Generator_Compare> Constraint_Generator_Heap;

    Stack<std::pair<unsigned,unsigned>>* _distinct_sort_constraints;
    Stack<std::pair<unsigned,unsigned>>* _strict_distinct_sort_constraints;

    /**
     * Constraints are at the same time used as generators.
     */
    Constraint_Generator_Heap _constraints_generators;

    unsigned _maxWeightSoFar;

    bool _skippedSomeSizes;

    // Stack<Constraint_Generator*> _old_generators; // keeping old generators degraded performance on average ...

  protected:
    bool checkConstriant(DArray<unsigned>& newSortSizes, Constraint_Generator_Vals& constraint);

  public:
    CLASS_NAME(FiniteModedlBuilder::HackyDSAE);
    USE_ALLOCATOR(FiniteModelBuilder::HackyDSAE);

    HackyDSAE() : _maxWeightSoFar(0) {}

    bool init(unsigned _startSize, DArray<unsigned>&, Stack<std::pair<unsigned,unsigned>>& dsc, Stack<std::pair<unsigned,unsigned>>& sdsc) override {
      _skippedSomeSizes = (_startSize > 1);
      _distinct_sort_constraints = &dsc;
      _strict_distinct_sort_constraints = &sdsc;
      return true;
    }

    bool isFmbComplete(unsigned noDomains) override { return (noDomains <= 1) && !_skippedSomeSizes; }
    void learnNogood(Constraint_Generator_Vals& nogood, unsigned weight) override;
    bool increaseModelSizes(DArray<unsigned>& newSortSizes, DArray<unsigned>& sortMaxes) override;
  };

#if VZ3
  class SmtBasedDSAE : public DSAEnumerator {
    z3::context _context;
    z3::solver  _smtSolver;
    unsigned _lastWeight;
    DArray<z3::expr*> _sizeConstants;
    bool _skippedSomeSizes;
  protected:
    unsigned loadSizesFromSmt(DArray<unsigned>& szs);
    void reportZ3OutOfMemory();
  public:
    // the following is not sufficient, since z3::solver and z3::context allocate internally
    CLASS_NAME(FiniteModedlBuilder::SmtBasedDSAE);
    USE_ALLOCATOR(FiniteModelBuilder::SmtBasedDSAE);

    SmtBasedDSAE() : _smtSolver(_context) {}

    bool init(unsigned, DArray<unsigned>&, Stack<std::pair<unsigned,unsigned>>&, Stack<std::pair<unsigned,unsigned>>&) override;
    void learnNogood(Constraint_Generator_Vals& nogood, unsigned weight) override;
    bool increaseModelSizes(DArray<unsigned>& newSortSizes, DArray<unsigned>& sortMaxes) override;
    bool isFmbComplete(unsigned) override { return !_skippedSomeSizes; }
  };
#endif

  // the sort constraints from injectivity/surjectivity
  // pairs of distinct sorts where pair.first >= pair.second
  Stack<std::pair<unsigned,unsigned>> _distinct_sort_constraints;
  // pairs of distinct sorts where pair.first > pair.second
  Stack<std::pair<unsigned,unsigned>> _strict_distinct_sort_constraints;

  // Record the number of constants in the problem per distinct sort
  DArray<unsigned> _distinctSortConstantCount;
  // min and max sizes for distinct sorts
  DArray<unsigned> _distinctSortMins;
  DArray<unsigned> _distinctSortMaxs;
  //unsigned _maxModelSizeAllSorts;

public: // debugging
    static void output_cg(Constraint_Generator_Vals& cgv) {
      cout << "[";
      for (unsigned i = 0; i < cgv.size(); i++) {
        cout << cgv[i].second;
        switch(cgv[i].first) {
        case EQ:
          cout << "=";
          break;
        case LEQ:
          cout << ">";
          break;
        case GEQ:
          cout << "<";
          break;
        case STAR:
          cout << "*";
          break;
        default:
          ASSERTION_VIOLATION;
        }
        if (i < cgv.size()-1) {
          cout << ", ";
        }
      }
      cout << "]";
    }

};
}

#endif // __FiniteModelBuilder__
