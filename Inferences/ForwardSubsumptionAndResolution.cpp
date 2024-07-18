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
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution.
 */
/**
 * The subsumption and subsumption resolution are described in the papers:
 * - 2022: "First-Order Subsumption via SAT Solving." by Jakob Rath, Armin Biere and Laura Kovács
 * - 2023: "SAT-Based Subsumption Resolution" by Robin Coutelier, Jakob Rath, Michael Rawson and
 *         Laura Kovács
 * - 2024: "SAT Solving for Variants of First-Order Subsumption" by Robin Coutelier, Jakob Rath,
 *         Michael Rawson, Armin Biere and Laura Kovács
 *
 * In particular, this file implements the loop optimization described in 2023 and 2024.
 */

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Inferences/ForwardSubsumptionAndResolution.hpp"

namespace Inferences {
using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution(bool subsumptionResolution, bool mutualSetupSR)
    : _subsumptionResolution(subsumptionResolution)
    , _mutualSetupSR(mutualSetupSR)
    , satSubs()
{
  // The mutual setup does not make sense if subsumption resolution is not performed
  ASS(!mutualSetupSR || subsumptionResolution)
}

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
}

void ForwardSubsumptionAndResolution::detach()
{
  _unitIndex = 0;
  _fwIndex = 0;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

/// @brief Set of clauses that were already checked
static DHSet<Clause *> checkedClauses;

bool ForwardSubsumptionAndResolution::perform(Clause *cl,
                                              Clause *&replacement,
                                              ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  ASS(replacement == nullptr)

  unsigned clen = cl->length();
  if (clen == 0)
    return false;

  /// @brief Conclusion of the subsumption resolution if successful
  Clause *conclusion = nullptr;
  /// @brief Premise of either subsumption or subsumption resolution
  Clause *premise = nullptr;

  checkedClauses.reset();

  Clause *mcl;

  /*******************************************************/
  /*              SUBSUMPTION UNIT CLAUSE                */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption since
  // L = a where a is a single literal
  // M = b v C where σ(a) = b is a given from the index
  // Therefore L subsumes M
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, false, false);
    if (it.hasNext()) {
      mcl = it.next().data->clause;
      premise = mcl;
      ASS(ColorHelper::compatible(cl->color(), premise->color()))
      premises = pvi(getSingletonIterator(premise));
      env.statistics->forwardSubsumed++;
      return true;
    }
  }

  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  // For each clauses mcl, first check for subsumption, then for subsumption resolution
  // During subsumption, setup the subsumption resolution solver. This is an overhead
  // largely compensated because the success rate of subsumption is fairly low, and
  // in case of failure, having the solver ready is a great saving on subsumption resolution
  //
  // Since subsumption is stronger than subsumption resolution, if a subsumption resolution is found,
  // keep it until the end of the loop to make sure no subsumption is possible.
  // Only when it has been checked that subsumption is not possible does the conclusion of
  // subsumption resolution become relevant
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().data->clause;
      // If we do not use the mutual setup, there is no need to store which clauses were already checked
      if (_mutualSetupSR && !checkedClauses.insert(mcl))
        continue;

      bool checkSR = _subsumptionResolution && !conclusion &&
                     _mutualSetupSR && // the mutual setup can be disabled when a lot of subsumptions should succeed. Reducing the optimization overhead
                    (_checkLongerClauses || mcl->length() <= clen);

      // if mcl is longer than cl, then it cannot subsume cl but still could be resolved
      bool checkS = mcl->length() <= clen;
      if (checkS) {
        if (satSubs.checkSubsumption(mcl, cl, checkSR)) {
          ASS(replacement == nullptr)
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          return true;
        }
      }
      if (checkSR) {
        // In this case, the literals come from the non complementary list, and there is therefore
        // a low chance of it being resolved. However, in the case where there is no negative match,
        // checkSubsumption resolution is very fast after subsumption, since filling the match set
        // for subsumption will have already detected that subsumption resolution is impossible
        conclusion = satSubs.checkSubsumptionResolution(mcl, cl, checkS);
        if (conclusion) {
          ASS(premise == nullptr)
          // cannot override the premise since the loop would have ended otherwise
          // the premise will be overriden if a subsumption is found
          premise = mcl;
        }
      }
    }
  }

  if (conclusion) {
    premises = pvi(getSingletonIterator(premise));
    replacement = conclusion;
    env.statistics->forwardSubsumptionResolution++;
    return true;
  }
  else if (!_subsumptionResolution)
    return false;

  /*******************************************************/
  /*         SUBSUMPTION RESOLUTION UNIT CLAUSE          */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption resolution since
  // L = a where a is a single literal
  // M = ¬b v C where σ(a) = ¬b is a given from the index
  // Therefore M can be replaced by C
  //
  // This behavior can be chained and several resolution can happen at the same time
  // The negatively matching literals are stacked and removed at the same time
  // However, some experiments showed that chaining subsumption resolutions yields poor performance
  // The intuition for this problem is that the intermidiate clauses can sometimes be useful.
  // This is why we do not chain subsumption resolutions.
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, true, false);
    if (it.hasNext()) {
      mcl = it.next().data->clause;
      ASS(mcl->length() == 1)
      replacement = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, lit, mcl);
      premises = pvi(getSingletonIterator(mcl));
      env.statistics->forwardSubsumptionResolution++;
      return true;
    }
  }

  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  // Check for the last clauses that are negatively matched in the index.
  // When not using the mutual setup, we are still guaranteed to find all
  // the good subsumption resolution candidates with the negative index
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().data->clause;
      // If we do not use the mutual setup, checkedClauses should be empty
      ASS(_mutualSetupSR || checkedClauses.isEmpty())
      if (_mutualSetupSR && !checkedClauses.insert(mcl))
        continue;
      if (!_checkLongerClauses && mcl->length() > clen)
        continue;
      conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      if (conclusion) {
        ASS(premise == nullptr)
        premise = mcl;
        replacement = conclusion;
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumptionResolution++;
        return true;
      }
    }
  }

  return false;
}  // perform


} // namespace Inferences
