/**
 * @file IGAlgorithm.hpp
 * Defines class IGAlgorithm.
 */

#ifndef __IGAlgorithm__
#define __IGAlgorithm__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "SAT/SATSolver.hpp"

#include "Shell/Statistics.hpp"

#include "Grounder.hpp"

namespace InstGen {

using namespace Kernel;
using namespace Indexing;
using namespace SAT;
using namespace Shell;

class IGAlgorithm {
public:
  typedef Statistics::TerminationReason TerminationReason;

  IGAlgorithm();

  void addInputClauses(ClauseIterator it) {
    addClauses(it);
  }

  TerminationReason process();
private:

  void addClauses(ClauseIterator it);
  void addClause(Clause* cl);

  void collectSelected(LiteralSubstitutionTree& acc);
  void tryGeneratingInstances(Clause* cl, unsigned litIdx, LiteralSubstitutionTree& selected);
  Clause* generateClause(Clause* orig, ResultSubstitution& subst, bool isQuery);
  void generateInstances();

  bool isSelected(Literal* lit);


  Grounder _gnd;
  SATSolverSCP _satSolver;

  /** Clauses that weren't yet added into the SATSolver */
  SATClauseStack _unprocessed;
  /** Clauses that are inside the SATSolver */
  SATClauseStack _active;

  ClauseVariantIndex _variantIdx;

  DHMap<SATClause*,Clause*> _s2c;
  DHMap<Clause*,SATClause*> _c2s;
};

}

#endif // __IGAlgorithm__
