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
 * @file BackwardSubsumptionAndResolution.cpp
 * Implements class BackwardSubsumptionAndResolution.
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

#include "Kernel/Clause.hpp"
#include "Lib/List.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "BackwardSubsumptionAndResolution.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  BackwardSimplificationEngine::attach(salg);
  _bwIndex = static_cast<BackwardSubsumptionIndex *>(
      _salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE)
  );
}

void BackwardSubsumptionAndResolution::detach()
{
  _bwIndex = 0;
  _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}


void BackwardSubsumptionAndResolution::perform(Clause *cl,
                                               BwSimplificationRecordIterator &simplifications)
{
  ASSERT_VALID(*cl)
  ASS(_bwIndex)
  simplifications = BwSimplificationRecordIterator::getEmpty();

  if (!_subsumption && !_subsumptionResolution) {
    return;
  }

  _checked.reset();

  // contains the list of simplifications found so far
  List<BwSimplificationRecord> *simplificationBuffer = List<BwSimplificationRecord>::empty();

  /********************************************************/
  /*                      cl is UNIT                      */
  /********************************************************/
  // cl is a unit clause and will subsume all clauses that contain its literal
  // and will be resolved with all clauses that contain its negation
  if (cl->length() == 1) {
    Literal *lit = (*cl)[0];
    // Check for the subsumptions
    if (_subsumption) {
      /***************************************************/
      /*            SUBSUMPTION UNIT CLAUSE              */
      /***************************************************/
      auto it = _bwIndex->getInstances(lit, false, false);
      while (it.hasNext()) {
        Clause *icl = it.next().data->clause;
        if (!_checked.insert(icl))
          continue;
        env.statistics->backwardSubsumed++;
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
      }
    }
    if (_subsumptionResolution) {
      /***************************************************/
      /*      SUBSUMPTION RESOLUTION UNIT CLAUSE         */
      /***************************************************/
      auto it = _bwIndex->getInstances(lit, true, false);
      while (it.hasNext()) {
        auto res = it.next();
        Clause *icl = res.data->clause;
        if (!_checked.insert(icl))
          continue;
        Clause *conclusion = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(icl, res.data->literal, cl, /*forward=*/false);
        ASS(conclusion)
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
    if (simplificationBuffer)
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    return;
  }

  if (_subsumptionByUnitsOnly && _srByUnitsOnly) {
    ASS(!simplificationBuffer)
    if (simplificationBuffer)
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    return;
  }

  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  // We use the optimization from Krystof Hoder and only search the instances of the least matchable
  // literal. Indeed, since for subsumption and subsumption resolution, each literal in the subsuming
  // clause S must be matched at least one literal in the subsumed clause M (idem for SR).
  // Therefore checking the instances of the least matchable literal will limit the number of candidates
  // for both subsumption and subsumption resolution.
  // For now, the least matchable literal is the heaviest literal in the clause. But this heuristic
  // could probably be improved.
  Literal* lit = (*cl)[0];
  unsigned lmVal = lit->weight();
  for(unsigned i = 1; i < cl->length(); i++) {
    Literal* curr = (*cl)[i];
    unsigned currVal = curr->weight();
    if(currVal > lmVal) {
      lit = curr;
      lmVal = currVal;
    }
  }

  if (!_subsumptionByUnitsOnly) {
    // find the positively matched literals
    auto it = _bwIndex->getInstances(lit, false, false);
    while (it.hasNext()) {
      Clause *icl = it.next().data->clause;
      if (!_checked.insert(icl))
        continue;
      // check subsumption and setup subsumption resolution at the same time
      bool checkS = _subsumption && !_subsumptionByUnitsOnly;
      bool checkSR = _subsumptionResolution && !_srByUnitsOnly;
      if (checkS) {
        if (_satSubs.checkSubsumption(cl, icl, checkSR)) {
          env.statistics->backwardSubsumed++;
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
          continue;
        }
      }
      if (checkSR) {
        // check subsumption resolution
        Clause *conclusion = _satSubs.checkSubsumptionResolution(cl, icl, /*forward=*/false, checkS); // use the previous setup only if subsumption was checked
        if (conclusion) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
        }
      }
    }
  }

  /*******************************************************/
  /*       SUBSUMPTION RESOLUTION MULTI-LITERAL          */
  /*******************************************************/
  if (_subsumptionResolution && !_srByUnitsOnly) {
    // find the negatively matched literals
    // We can use the same least matchable literal as before since our method is agnostic to the
    // flipped literal
    auto it = _bwIndex->getInstances(lit, true, false);
    while (it.hasNext()) {
      Clause *icl = it.next().data->clause;
      if (!_checked.insert(icl))
        continue;
      // check subsumption resolution
      Clause *conclusion = _satSubs.checkSubsumptionResolution(cl, icl, /*forward=*/false, false);
      if (conclusion) {
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
  }

  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }
}

} // namespace Inferences
