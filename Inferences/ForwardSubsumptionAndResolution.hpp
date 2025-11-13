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
 * @file ForwardSubsumptionAndResolution.hpp
 * Defines class ForwardSubsumptionAndResolution.
 */

#ifndef __Forward_Subsumption_And_Resolution__
#define __Forward_Subsumption_And_Resolution__

#include "Inferences/InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Indexing/LiteralIndex.hpp"

namespace Inferences {
class ForwardSubsumptionAndResolution
    : public ForwardSimplificationEngine {
public:
  ForwardSubsumptionAndResolution(bool subsumptionResolution = true);

  /**
   * Attaches the inference engine to the saturation algorithm.
   * Also fetches the unit and forward index from the saturation algorithm.
   * @param salg the saturation algorithm
   */
  void attach(Saturation::SaturationAlgorithm *salg) override;

  /**
   * Detaches the inference engine from the saturation algorithm.
   * Also clears the unit and forward index.
   */
  void detach() override;

  /**
   * @brief Performs forward subsumption and resolution on the given clause.
   * If the clause is subsumed, then the @b premises iterator is set to the subsuming clause and the function returns true.
   * If the clause is resolved and subsumed, then the @b replacement clause is set to the conclusion clause, the @b premises iterator is set to the subsuming clause and the function returns true.
   * If the clause is not subsumed or resolved and subsumed, then the function returns false.
   * @param cl the clause to be simplified
   * @param replacement the references to the replacement clause
   * @param premises the reference to the premises of the inference
   * @return true if the clause was simplified
   */
  bool perform(Kernel::Clause *cl,
               Kernel::Clause *&replacement,
               Kernel::ClauseIterator &premises) override;

private:
  /// @brief Unit index of the saturation algorithm
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  /// @brief Forward index containing the clauses with which the inference engine can perform forward subsumption and resolution
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;

  /// @brief Parameter to enable or disable subsumption resolution
  /// @note If the parameter is set to false, then the inference engine will only perform forward subsumption
  bool _subsumptionResolution;

  bool _checkLongerClauses = true;

  /// @brief Engine performing subsumption and subsumption resolution using a sat solver
  SATSubsumption::SATSubsumptionAndResolution satSubs;
};

}; // namespace Inferences

#endif /* __Forward_Subsumption_And_Resolution__ */
