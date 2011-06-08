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
  typedef InferenceStore::UnitSpec UnitSpec;

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
	isParentOfLeft(false), isParentOfRight(false), leadsToColor(false) {}

    Color color;

    UnitState state;

    bool isRefutation;
    bool isParentOfLeft;
    bool isParentOfRight;

    /** True if unit has some non-transparent ancestor (doesn't need to be immediate) */
    bool leadsToColor;
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
    /** Formula is in the digest */
    D,
    /** Atom appears is in the digest */
    V
  };

  SMTConstant pred(PredType t, string node);
  SMTConstant costFunction();

  void addDistinctColorsFormula(string n);

  void addGreyNodePropertiesFormula(string n, ParentSummary& parents);
  void addColoredParentPropertiesFormulas(string n, ParentSummary& parents);
  void addNodeFormulas(string n, ParentSummary& parents);

private:
  //generating the weight-minimizing part of the problem

  void addAtomImplicationFormula(UnitSpec u);
  void addCostFormula();

  void collectAtoms(FormulaUnit* f, Stack<string>& atoms);
  string getLiteralId(Literal* l);
  void collectAtoms(UnitSpec u, Stack<string>& atoms);

  DHMap<Literal*, string> _atomIds;
  DHMap<string, string> _formulaAtomIds;

  typedef DHMap<string, unsigned> WeightMap;
  WeightMap _atomWeights;

private:
  //and here is the glue

  void collectSlicedOffNodes(SMTSolverResult& solverResult, DHSet<UnitSpec>& acc);

  string getUnitId(UnitSpec u);

  void addNodeFormulas(UnitSpec u);

  void addAllFormulas();

  bool _noSlicing;
  SMTBenchmark _resBenchmark;
};

}

#endif // __InterpolantMinimizer__
