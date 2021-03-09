
/*
 * File ForwardSubsumptionAndResolution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions.
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide.
 */
/**
 * @file ForwardSubsumptionAndResolution.hpp
 * Defines class ForwardSubsumptionAndResolution.
 */


#ifndef __ForwardSubsumptionAndResolution__
#define __ForwardSubsumptionAndResolution__


#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "SMTSubsumption/SMTSubsumption.hpp"
#include "Lib/STL.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


class SubsumptionLogger;

class ForwardSubsumptionAndResolution
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardSubsumptionAndResolution);
  USE_ALLOCATOR(ForwardSubsumptionAndResolution);

  ForwardSubsumptionAndResolution(bool subsumptionResolution=true);
  ~ForwardSubsumptionAndResolution();

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause);

  static ForwardSubsumptionAndResolution* getInstance();
  void printStats(std::ostream& out);

private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;

  bool _subsumptionResolution;

  SMTSubsumption::ProofOfConcept smtsubs;
  std::unique_ptr<SubsumptionLogger> m_logger;

  // Store numDecisions as histogram
  // m_numDecisions_frequence[numDecisions] = absolute number of MLMatcher calls that return numDecisions
  vvector<int64_t> m_numDecisions_frequency;
  // only those where MLMatcher returned 'true'
  vvector<int64_t> m_numDecisions_successes;
};


};

#endif /* __ForwardSubsumptionAndResolution__ */
