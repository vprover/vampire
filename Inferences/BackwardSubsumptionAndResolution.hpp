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
 * @file BackwardSubsumptionAndResolution.hpp
 * Defines class BackwardSubsumptionAndResolution.
 */

#ifndef __BackwardSubsumptionAndResolution__
#define __BackwardSubsumptionAndResolution__

#include "Lib/DHSet.hpp"
#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

namespace Inferences {

class BackwardSubsumptionAndResolution
    : public BackwardSimplificationEngine {

public:
  BackwardSubsumptionAndResolution(bool subsumption, bool subsumptionByUnitsOnly, bool subsumptionResolution, bool srByUnitsOnly)
    : _subsumption(subsumption), _subsumptionResolution(subsumptionResolution), _subsumptionByUnitsOnly(subsumptionByUnitsOnly), _srByUnitsOnly(srByUnitsOnly)
  {
    // do nothing
  }
  ~BackwardSubsumptionAndResolution() override {}

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;
  void perform(Kernel::Clause *premise, Inferences::BwSimplificationRecordIterator &simplifications) override;

private:
  /// @brief True if the inference engine should perform subsumption
  bool _subsumption;
  /// @brief True if the inference engine should perform subsumption resolution
  bool _subsumptionResolution;
  /// @brief True if the inference engine should perform subsumption by unit clauses only
  bool _subsumptionByUnitsOnly;
  /// @brief True if the inference engine should perform subsumption resolution by unit clauses only
  bool _srByUnitsOnly;

  /// @brief Backward index for subsumption and subsumption resolution candidates
  Indexing::BackwardSubsumptionIndex *_bwIndex;
  /// @brief SAT-based subsumption and subsumption resolution engine
  SATSubsumption::SATSubsumptionAndResolution _satSubs;
  /// @brief Set of clauses that have already been checked for subsumption and/or subsumption resolution
  Lib::DHSet<Clause *> _checked;

};

}; // namespace Inferences

#endif /* __BackwardSubsumptionAndResolution__ */
