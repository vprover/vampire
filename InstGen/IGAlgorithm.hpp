/**
 * @file IGAlgorithm.hpp
 * Defines class IGAlgorithm.
 */

#ifndef __IGAlgorithm__
#define __IGAlgorithm__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "SAT/SATSolver.hpp"

#include "Shell/Statistics.hpp"

#include "Kernel/Grounder.hpp"

namespace InstGen {

using namespace Kernel;
using namespace Inferences;
using namespace Indexing;
using namespace SAT;
using namespace Shell;

class IGAlgorithm {
public:
  typedef Statistics::TerminationReason TerminationReason;

  IGAlgorithm();
  ~IGAlgorithm();

  void addInputClauses(ClauseIterator it) {
    addClauses(it);
  }

  TerminationReason run();
private:

  void addClauses(ClauseIterator it);
  void addClause(Clause* cl);

  void processUnprocessed();

  void collectSelected(LiteralSubstitutionTree& acc);
  void tryGeneratingInstances(Clause* cl, unsigned litIdx, LiteralSubstitutionTree& selected);
  void tryGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery);
  void generateInstances();

  bool isSelected(Literal* lit);


  IGGrounder _gnd;
  SATSolverSCP _satSolver;

  /** Clauses that weren't yet added into the SATSolver */
  RCClauseStack _unprocessed;
  /** Clauses that are inside the SATSolver */
  RCClauseStack _active;

  ClauseVariantIndex _variantIdx;

  DuplicateLiteralRemovalISE _dlr;

  SaturationAlgorithmSP _dummy;
};

}

#endif // __IGAlgorithm__
