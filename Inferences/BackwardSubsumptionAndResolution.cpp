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

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "ForwardSubsumptionAndResolution.hpp"
#include "BackwardSubsumptionAndResolution.hpp"

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
#include "BackwardSubsumptionResolution.hpp"
#include "SLQueryBackwardSubsumption.hpp"
#endif

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

#define BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS 1
#define SEPARATE_LOOPS_BACKWARD 1

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
static unsigned nSubsumptions = 0;
static unsigned nResolutions = 0;
static unsigned nSuccessSubsumptions = 0;
static unsigned nSuccessResolutions = 0;
static unsigned nUnitSubsumptions = 0;
static unsigned nUnitResolutions = 0;
#endif

void BackwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  CALL("BackwardSubsumptionAndResolution::attach");
  BackwardSimplificationEngine::attach(salg);
  _index = static_cast<BackwardSubsumptionIndex *>(
      _salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE));
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
  _slqbs.attach(salg);
  _bsr.attach(salg);
#endif
}

void BackwardSubsumptionAndResolution::detach()
{
  CALL("BackwardSubsumptionAndResolution::detach");
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
  env.beginOutput();
  env.out() << "*******************************************************************" << endl;
  env.out() << "BackwardSubsumptionAndResolution: " << nSubsumptions << " subsumptions, " << nResolutions << " resolutions, " << nSuccessSubsumptions << " successful subsumptions, " << nSuccessResolutions << " successful resolutions" << endl;
  env.out() << "*******************************************************************" << endl;
  env.endOutput();
#endif
  _index = 0;
  _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

void BackwardSubsumptionAndResolution::perform(Clause *cl,
                                               BwSimplificationRecordIterator &simplifications)
{
  CALL("BackwardSubsumptionAndResolution::perform");
  ASSERT_VALID(*cl);
  ASS(_index);
  simplifications = BwSimplificationRecordIterator::getEmpty();

  if (!_subsumption && !_subsumptionResolution) {
    return;
  }

  static DHSet<Clause *> checkedClauses;
  checkedClauses.reset();

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
  static DHSet<Clause *> subsumedSet;
  subsumedSet.reset();
#endif

  /********************************************************/
  /*                      cl is UNIT                      */
  /********************************************************/
  List<BwSimplificationRecord> *simplificationBuffer = List<BwSimplificationRecord>::empty();
  // cl is a unit clause and will subsume all clauses that contain its literal
  // and will be resolved with all clauses that contain its negation
  if (cl->length() == 1) {
    Literal *lit = (*cl)[0];
    // Check for the subsumptions
    if (_subsumption) {
      SLQueryResultIterator rit = _index->getInstances(lit, false, false);
      while (rit.hasNext()) {
        SLQueryResult qr = rit.next();
        Clause *icl = qr.clause;
        if (!checkedClauses.insert(icl)) {
          continue;
        }
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
        subsumedSet.insert(icl);
#endif
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
        nSubsumptions++;
        nSuccessSubsumptions++;
        nUnitSubsumptions++;
#endif
      }
    }
    // Check for subsumption resolution
    if (_subsumptionResolution) {
      SLQueryResultIterator rit = _index->getInstances(lit, true, false);
      while (rit.hasNext()) {
        SLQueryResult qr = rit.next();
        Clause *icl = qr.clause;
        if (!checkedClauses.insert(icl)) {
          continue;
        }
        Clause *resCl = ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(icl, lit, cl);
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
        nResolutions++;
        nSuccessResolutions++;
        nUnitResolutions++;
#endif
      }
    }
  }
  if (_subsumptionByUnitsOnly && _srByUnitsOnly) {
    if (simplificationBuffer) {
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    }
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
    goto check_correctness;
#else
    return;
#endif
  }

#if SEPARATE_LOOPS_BACKWARD
  /********************************************************/
  /*             SUBSUMPTION cl is NOT UNIT               */
  /********************************************************/
  if (!_subsumptionByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the positively matched literals
      SLQueryResultIterator rit = _index->getInstances(lit, false, false);
      while (rit.hasNext()) {
        SLQueryResult qr = rit.next();
        Clause *icl = qr.clause;
        if (!checkedClauses.insert(icl)) {
          continue;
        }
        // check subsumption and setup subsumption resolution at the same time
        if (_subsumption && satSubs.checkSubsumption(cl, icl, _subsumptionResolution)) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
          subsumedSet.insert(icl);
#endif
        }
      }
    }
  }

  if (!_subsumptionResolution || _srByUnitsOnly) {
    if (simplificationBuffer) {
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    }
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
    goto check_correctness;
#else
    return;
#endif
  }
  /********************************************************/
  /*        SUBSUMPTION RESOLUTION cl is NOT UNIT         */
  /********************************************************/
  checkedClauses.reset();
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    // find the negatively matched literals
    SLQueryResultIterator rit = _index->getInstances(lit, true, false);
    if(!rit.hasNext()) {
      rit = _index->getInstances(lit, false, false);
    }
    bool firstPass = true;
    while (rit.hasNext()) {
      SLQueryResult qr = rit.next();
      Clause *icl = qr.clause;
      if(firstPass && !rit.hasNext()) {
        // need to check for the positive matches as well.
        firstPass = false;
        rit = _index->getInstances(lit, false, false);
      }
      if (!checkedClauses.insert(icl)) {
        continue;
      }

      // check subsumption resolution
      Clause *resCl = satSubs.checkSubsumptionResolution(cl, icl, false);
      if (resCl) {
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
      }
    }
  }
  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }
#else
  /********************************************************/
  /*      SUBSUMPTION AND RESOLUTION cl is NOT UNIT       */
  /********************************************************/
  if (!_subsumptionByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the positively matched literals
      SLQueryResultIterator rit = _index->getInstances(lit, false, false);
      while (rit.hasNext()) {
        SLQueryResult qr = rit.next();
        Clause *icl = qr.clause;
        if (!checkedClauses.insert(icl)) {
          continue;
        }
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
        nSubsumptions++;
#endif
        // check subsumption and setup subsumption resolution at the same time
        if (_subsumption && satSubs.checkSubsumption(cl, icl, _subsumptionResolution)) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
          subsumedSet.insert(icl);
#endif
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
          nSuccessSubsumptions++;
#endif
        }
        else if (_subsumptionResolution) {
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
          nResolutions++;
#endif
          // check subsumption resolution
          Clause *resCl = satSubs.checkSubsumptionResolution(cl, icl, _subsumption);
          if (resCl) {
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
            nSuccessResolutions++;
#endif
          }
        }
      }
    }
  }

  if (!_subsumptionResolution || _srByUnitsOnly) {
    if (simplificationBuffer) {
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    }
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
    goto check_correctness;
#else
    return;
#endif
  }
  /********************************************************/
  /*        SUBSUMPTION RESOLUTION cl is NOT UNIT         */
  /********************************************************/
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    // find the negatively matched literals
    SLQueryResultIterator rit = _index->getInstances(lit, true, false);
    while (rit.hasNext()) {
      SLQueryResult qr = rit.next();
      Clause *icl = qr.clause;
      if (!checkedClauses.insert(icl)) {
        continue;
      }
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
      nResolutions++;
#endif
      // check subsumption resolution
      Clause *resCl = satSubs.checkSubsumptionResolution(cl, icl, false);
      if (resCl) {
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
#if BACKWARD_SUBSUMPTION_AND_RESOLUTION_STATS
        nSuccessResolutions++;
#endif
      }
    }
  }
  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }
#endif
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
check_correctness:
  // The efficiency of this code is very terrible, but it is only used for debugging
  // Get the results from the old implementation
  DHSet<Clause *> checkedSimplifications;
  if (_subsumption) {
    BwSimplificationRecordIterator oldSimplifications = BwSimplificationRecordIterator::getEmpty();
    _slqbs.perform(cl, oldSimplifications);
    while (oldSimplifications.hasNext()) {
      BwSimplificationRecord rec = oldSimplifications.next();
      checkedSimplifications.insert(rec.toRemove);
      auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
      bool found = false;
      while (it.hasNext()) {
        BwSimplificationRecord rec2 = it.next();
        if (rec2.replacement == nullptr && rec2.toRemove == rec.toRemove) {
          found = true;
          break;
        }
      }
      if (!found) {
        cout << "------ SUBSUMPTION FALSE NEGATIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;

        if (checkedClauses.contains(rec.toRemove)) {
          cout << "Clause was checked" << endl;
        }
        else {
          cout << "Clause was NOT checked" << endl;
        }
      }
    }
    auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
    while (it.hasNext()) {
      BwSimplificationRecord rec = it.next();
      if (rec.replacement == nullptr && !checkedSimplifications.contains(rec.toRemove)) {
        cout << "------ SUBSUMPTION FALSE POSITIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;

        if (checkedClauses.contains(rec.toRemove)) {
          cout << "Clause was checked" << endl;
        }
        else {
          cout << "Clause was NOT checked" << endl;
        }
      }
    }
  }

  if (_subsumptionResolution) {
    BwSimplificationRecordIterator oldSimplifications = BwSimplificationRecordIterator::getEmpty();
    _bsr.perform(cl, oldSimplifications);
    while (oldSimplifications.hasNext()) {
      BwSimplificationRecord rec = oldSimplifications.next();
      checkedSimplifications.insert(rec.toRemove);
      auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
      bool found = false;
      while (it.hasNext()) {
        BwSimplificationRecord rec2 = it.next();
        if (rec2.replacement != nullptr && rec2.toRemove == rec.toRemove) {
          found = true;
          break;
        }
      }
      if (!found && !subsumedSet.contains(rec.toRemove)) {
        cout << "------ SR FALSE NEGATIVE ------" << endl;
        cout << "base    : " << *cl << endl;
        cout << "instance: " << rec.toRemove->toNiceString() << endl;
        cout << "Resolution: " << rec.replacement->toNiceString() << endl;
        if (checkedClauses.contains(rec.toRemove)) {
          cout << "Clause was checked" << endl;
        }
        else {
          cout << "Clause was NOT checked" << endl;
        }
      }
    }
    auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
    while (it.hasNext()) {
      BwSimplificationRecord rec = it.next();
      if (rec.replacement != nullptr && !checkedSimplifications.contains(rec.toRemove)) {
        cout << "------ SR FALSE POSITIVE ------" << endl;
        cout << "base    : " << *cl << endl;
        cout << "instance: " << rec.toRemove->toNiceString() << endl;
        cout << "Resolution: " << rec.replacement->toNiceString() << endl;

        if (checkedClauses.contains(rec.toRemove)) {
          cout << "Clause was checked" << endl;
        }
        else {
          cout << "Clause was NOT checked" << endl;
        }
      }
    }
  }

#endif
}

} // namespace Inferences
