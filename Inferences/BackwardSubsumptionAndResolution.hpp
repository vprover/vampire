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
  BackwardSubsumptionAndResolution(SaturationAlgorithm& salg);

  void perform(Kernel::Clause *premise, Inferences::BwSimplificationRecordIterator &simplifications) override;

private:
  /// @brief True if the inference engine should perform subsumption
  const bool _subsumption;
  /// @brief True if the inference engine should perform subsumption resolution
  const bool _subsumptionResolution;
  /// @brief True if the inference engine should perform subsumption by unit clauses only
  const bool _subsumptionByUnitsOnly;
  /// @brief True if the inference engine should perform subsumption resolution by unit clauses only
  const bool _srByUnitsOnly;

  /// @brief Backward index for subsumption and subsumption resolution candidates
  std::shared_ptr<Indexing::BackwardSubsumptionIndex> _bwIndex;
  /// @brief SAT-based subsumption and subsumption resolution engine
  SATSubsumption::SATSubsumptionAndResolution _satSubs;
  /// @brief Set of clauses that have already been checked for subsumption and/or subsumption resolution
  Lib::DHSet<Clause*> _checked;

};

}; // namespace Inferences

#endif /* __BackwardSubsumptionAndResolution__ */
