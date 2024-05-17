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
#include "BackwardSubsumptionAndResolution.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/***************************************************************/
/*                        CORE METHODS                         */
/***************************************************************/
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

  // The set of clauses that are subsumed by cl
  static DHSet<Clause *> subsumedSet;
  subsumedSet.reset();
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
        subsumedSet.insert(icl);
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
        if (subsumedSet.contains(icl) || !_checked.insert(icl))
          continue;
        Clause *conclusion = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(icl, res.data->literal, cl);
        ASS(conclusion)
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
    goto finish;
  }

  if (_subsumptionByUnitsOnly && _srByUnitsOnly) {
    ASS(!simplificationBuffer)
    goto finish;
  }

  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  if (!_subsumptionByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
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
          if (satSubs.checkSubsumption(cl, icl, checkSR)) {
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
            subsumedSet.insert(icl);
            continue;
          }
        }
        if (checkSR) {
          // check subsumption resolution
          Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, checkS); // use the previous setup only if subsumption was checked
          if (conclusion)
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
        }
      }
    }
  }

  /*******************************************************/
  /*       SUBSUMPTION RESOLUTION MULTI-LITERAL          */
  /*******************************************************/
  if (_subsumptionResolution && !_srByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the negatively matched literals
      auto it = _bwIndex->getInstances(lit, true, false);
      while (it.hasNext()) {
        Clause *icl = it.next().data->clause;
        if (!_checked.insert(icl))
          continue;
        // check subsumption resolution
        Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, false);
        if (conclusion)
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
  }

finish:
  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }

  return;
}

} // namespace Inferences
