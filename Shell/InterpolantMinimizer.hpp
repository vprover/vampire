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
  InterpolantMinimizer(bool minimizeComponentCount=false, bool noSlicing=false,
      bool showStats=false, string statsPrefix="");
  ~InterpolantMinimizer();

  typedef InferenceStore::UnitSpec UnitSpec;
  typedef List<UnitSpec> USList;

  Formula* getInterpolant(Clause* refutation);

private:
  //proof tree traversing

  void traverse(Clause* refutation);

  struct TraverseStackEntry;

  enum UnitState {
    TRANSPARENT_PARENTS,
    HAS_LEFT_PARENT,
    HAS_RIGHT_PARENT
  };

  struct UnitInfo
  {
    UnitInfo() : state(TRANSPARENT_PARENTS), isRefutation(false),
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
    List<UnitSpec>* leftSuccessors;
    List<UnitSpec>* rightSuccessors;
    List<UnitSpec>* transparentSuccessors;
  };

  typedef DHMap<UnitSpec,UnitInfo> InfoMap;

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

    Stack<string> rParents;
    Stack<string> bParents;
    Stack<string> gParents;
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

  SMTConstant pred(PredType t, string node);
  SMTConstant costFunction();

  void addDistinctColorsFormula(string n);

  void addLeafNodePropertiesFormula(string n);
  void addGreyNodePropertiesFormula(string n, ParentSummary& parents);
  void addColoredParentPropertiesFormulas(string n, ParentSummary& parents);
  void addNodeFormulas(string n, ParentSummary& parents);

  void addFringeFormulas(UnitSpec u);
private:
  //generating the weight-minimizing part of the problem

  void addAtomImplicationFormula(UnitSpec u);
  void addCostFormula();

  void collectAtoms(FormulaUnit* f, Stack<string>& atoms);
  string getComponentId(Clause* cl);
  void collectAtoms(UnitSpec u, Stack<string>& atoms);

  class ClauseSplitter;

  DHMap<Clause*, string> _atomIds;
  DHMap<string, string> _formulaAtomIds;

  typedef DHMap<string, unsigned> WeightMap;
  WeightMap _atomWeights;

  DHMap<string,UnitSpec> _unitsById;

  ClauseSplitter* _splitter;
private:
  //and here is the glue

  void collectSlicedOffNodes(SMTSolverResult& solverResult, DHSet<UnitSpec>& acc);

  string getUnitId(UnitSpec u);

  void addNodeFormulas(UnitSpec u);

  void addAllFormulas();

  bool _minimizeComponentCount;
  bool _noSlicing;
  bool _showStats;
  string _statsPrefix;
  SMTBenchmark _resBenchmark;
};

}

#endif // __InterpolantMinimizer__
