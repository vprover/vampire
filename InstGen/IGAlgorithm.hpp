/**
 * @file IGAlgorithm.hpp
 * Defines class IGAlgorithm.
 */

#ifndef __IGAlgorithm__
#define __IGAlgorithm__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/RatioKeeper.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/MainLoop.hpp"
#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseVariantIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"
#include "Inferences/URResolution.hpp"

#include "SAT/SATSolver.hpp"

#include "Saturation/AWPassiveClauseContainer.hpp"

#include "Shell/Options.hpp"
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

  IGAlgorithm(Problem& prb, const Options& opt);
  ~IGAlgorithm();

  GroundingIndex& getGroundingIndex() { return *_groundingIndex.ptr(); }

  ClauseIterator getActive();

protected:
  virtual void init();
  virtual MainLoopResult runImpl();
private:

  void addClause(Clause* cl);

  void restartWithCurrentClauses();
  void restartFromBeginning();


  void wipeIndexes();

  void processUnprocessed();
  void activate(Clause* cl, bool wasDeactivated=false);

  void deactivate(Clause* cl);
  void doReactivation();

  void selectAndAddToIndex(Clause* cl);
  void removeFromIndex(Clause* cl);

  void tryGeneratingInstances(Clause* cl, unsigned litIdx);
  void tryGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery, Clause* otherCl);

  bool isSelected(Literal* lit);

  Clause* getFORefutation(SATClause* satRefutation);


  void onResolutionClauseDerived(Clause* cl);
  void doResolutionStep();


  RatioKeeper _instGenResolutionRatio;


  IGGrounder _gnd;
  SATSolverSCP _satSolver;

  /** Used by global subsumption */
  ScopedPtr<GroundingIndex> _groundingIndex;
  ScopedPtr<GlobalSubsumption> _globalSubsumption;

  Options _saturationOptions;
  ScopedPtr<IndexManager> _saturationIndexManager;
  ScopedPtr<Problem> _saturationProblem;
  ScopedPtr<SaturationAlgorithm> _saturationAlgorithm;

//  ScopedPtr<UnitClauseLiteralIndex> _unitLitIndex;
//  ScopedPtr<NonUnitClauseLiteralIndex> _nonUnitLitIndex;
//  ScopedPtr<URResolution> _urResolution;
//  PlainClauseContainer _resolutionContainer;

  /** Clauses that weren't yet added into the SATSolver */
  RCClauseStack _unprocessed;
  /** Clauses that are inside the SATSolver but not used for instantiation */
  AWClauseContainer _passive;
  /** Clauses inside the SATSolver and used for instantiation */
  RCClauseStack _active;

  /** Clauses that need to be activated again because of the change in selection */
  ClauseStack _deactivated;
  DHSet<Clause*> _deactivatedSet;

  RCClauseStack _inputClauses;

  ClauseVariantIndex* _variantIdx;

  LiteralSubstitutionTree* _selected;

  DuplicateLiteralRemovalISE _duplicateLiteralRemoval;
  TautologyDeletionISE _tautologyDeletion;
};

}

#endif // __IGAlgorithm__
