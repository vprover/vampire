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
 * @file InterpolantMinimizer.hpp
 * Defines class InterpolantMinimizer.
 */

#ifndef __InterpolantMinimizer__
#define __InterpolantMinimizer__

#include "Lib/DHSet.hpp"
#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/InferenceStore.hpp"

#include "SMTFormula.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class InterpolantMinimizer
{
public:
  enum OptimizationTarget
  {
    OT_WEIGHT,
    OT_COUNT,
    OT_QUANTIFIERS
  };

  InterpolantMinimizer(OptimizationTarget target=OT_WEIGHT, bool noSlicing=false,
      bool showStats=false, vstring statsPrefix="");
  ~InterpolantMinimizer();

  typedef List<Unit*> UList;

  Formula* getInterpolant(Unit* refutation);
    
  typedef Signature::Symbol Symbol;
    
  void prettyPrint(Term* t, ostream& out);
  void prettyPrint(Symbol* symb, ostream& out);
  void prettyPrint(Formula* formula, ostream& out);



private:
  //proof tree traversing

  void traverse(Unit* refutationUnit);

  struct TraverseStackEntry;

  enum UnitState {
    TRANSPARENT_PARENTS,
    HAS_LEFT_PARENT,
    HAS_RIGHT_PARENT
  };

  struct UnitInfo
  {
    UnitInfo() : color(COLOR_INVALID), inputInheritedColor(COLOR_INVALID),
        state(TRANSPARENT_PARENTS), isRefutation(false),
	isParentOfLeft(false), isParentOfRight(false), leadsToColor(false),
	leftSuccessors(0), rightSuccessors(0), transparentSuccessors(0) {}

    Color color;
    Color inputInheritedColor;

    UnitState state;

    bool isRefutation;
    bool isParentOfLeft;
    bool isParentOfRight;

    /** True if unit has some non-transparent ancestor (doesn't need to be immediate) */
    bool leadsToColor;

    //TODO: fix memory leak caused by these lists
    List<Unit*>* leftSuccessors;
    List<Unit*>* rightSuccessors;
    List<Unit*>* transparentSuccessors;
  };

  typedef DHMap<Unit*,UnitInfo> InfoMap;

  InfoMap _infos;

private:
  //here is the code related to generating the SMT problem

  struct ParentSummary
  {
    void reset() {
      rParents.reset();
      bParents.reset();
      gParents.reset();
    }

    Stack<vstring> rParents;
    Stack<vstring> bParents;
    Stack<vstring> gParents;
  };

  enum PredType
  {
    /** Formula has red (i.e. left) color in its trace */
    R,
    /** Formula has blue (i.e. right) color in its trace */
    B,
    /** The trace of a formula is gray (i.e. transparent) */
    G,
    /** Formula is sliced off */
    S,
    /** Formula is a consequence of red symbol elimination */
    RC,
    /** Formula is a consequence of blue symbol elimination */
    BC,
    /** Red fringe */
    RF,
    /** Blue fringe */
    BF,
    /** Formula is in the digest */
    D,
    /** Atom appears is in the digest */
    V
  };

  SMTConstant pred(PredType t, vstring node);
  SMTConstant costFunction();

  void addDistinctColorsFormula(vstring n);

  void addLeafNodePropertiesFormula(vstring n);
  void addGreyNodePropertiesFormula(vstring n, ParentSummary& parents);
  void addColoredParentPropertiesFormulas(vstring n, ParentSummary& parents);
  void addNodeFormulas(vstring n, ParentSummary& parents);

  void addFringeFormulas(Unit* u);
    
private:
  //generating the weight-minimizing part of the problem

  void addAtomImplicationFormula(Unit* u);
  void addCostFormula();

  void collectAtoms(FormulaUnit* f, Stack<vstring>& atoms);
  vstring getComponentId(Clause* cl);
  void collectAtoms(Unit* u, Stack<vstring>& atoms);

  class ClauseSplitter;

  DHMap<Clause*, vstring> _atomIds;
  DHMap<vstring, vstring> _formulaAtomIds;

  typedef DHMap<vstring, unsigned> WeightMap;
  WeightMap _atomWeights;

  DHMap<vstring,Unit*> _unitsById;

  ClauseSplitter* _splitter;
private:
  //and here is the glue

  void collectSlicedOffNodes(SMTSolverResult& solverResult, DHSet<Unit*>& acc);

  vstring getUnitId(Unit* u);

  void addNodeFormulas(Unit* u);

  void addAllFormulas();

  OptimizationTarget _optTarget;
  bool _noSlicing;
  bool _showStats;
  vstring _statsPrefix;
  SMTBenchmark _resBenchmark;
};

}

#endif // __InterpolantMinimizer__
