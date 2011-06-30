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

#include "Kernel/MainLoop.hpp"
#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"

#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "SAT/SATSolver.hpp"

#include "Saturation/AWPassiveClauseContainer.hpp"

#include "Shell/Statistics.hpp"

#include "Kernel/Grounder.hpp"

namespace InstGen {

using namespace Kernel;
using namespace Inferences;
using namespace Indexing;
using namespace SAT;
using namespace Saturation;
using namespace Shell;

class IGAlgorithm : public MainLoop {
public:
  typedef Statistics::TerminationReason TerminationReason;

  IGAlgorithm();
  ~IGAlgorithm();

  virtual void addInputClauses(ClauseIterator it);

protected:
  virtual MainLoopResult runImpl();
private:

  void addClauses(ClauseIterator it);
  void addClause(Clause* cl);

  void processUnprocessed();

  void collectSelected(LiteralSubstitutionTree& acc);
  void tryGeneratingInstances(Clause* cl, unsigned litIdx, LiteralSubstitutionTree& selected);
  void tryGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery);
  void generateInstances();

  bool isSelected(Literal* lit);

  Clause* getFORefutation(SATClause* satRefutation);

  IGGrounder _gnd;
  SATSolverSCP _satSolver;

  /** Used by global subsumption */
  ScopedPtr<GroundingIndex> _groundingIndex;
  ScopedPtr<GlobalSubsumption> _globalSubsumption;

  /** Clauses that weren't yet added into the SATSolver */
  RCClauseStack _unprocessed;
  /** Clauses that are inside the SATSolver but not used for instantiation */
  AWClauseContainer _passive;
  /** Clauses inside the SATSolver and used for instantiation */
  RCClauseStack _active;

  ClauseVariantIndex _variantIdx;

  DuplicateLiteralRemovalISE _duplicateLiteralRemoval;
  TautologyDeletionISE _tautologyDeletion;
};

}

#endif // __IGAlgorithm__
