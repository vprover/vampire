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
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __SLQueryBackwardSubsumption__
#define __SLQueryBackwardSubsumption__

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;

class SLQueryBackwardSubsumption
: public BackwardSimplificationEngine
{
public:
  CLASS_NAME(SLQueryBackwardSubsumption);
  USE_ALLOCATOR(SLQueryBackwardSubsumption);

  SLQueryBackwardSubsumption(bool byUnitsOnly) : _byUnitsOnly(byUnitsOnly), _index(0) {}

  /**
   * Create SLQueryBackwardSubsumption rule with explicitely provided index,
   * independent of an SaturationAlgorithm.
   *
   * For objects created by this constructor, methods  @c attach()
   * and @c detach() must not be called.
   */
  SLQueryBackwardSubsumption(SimplifyingLiteralIndex* index, bool byUnitsOnly=false) : _byUnitsOnly(byUnitsOnly), _index(index) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  struct ClauseExtractorFn;
  struct ClauseToBwSimplRecordFn;

  bool _byUnitsOnly;
  SimplifyingLiteralIndex* _index;
};

};

#endif /* __SLQueryBackwardSubsumption__ */
