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

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

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
  _index = 0;
  _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

void BackwardSubsumptionAndResolution::perform(Clause *cl,
                                               BwSimplificationRecordIterator &simplifications)
{
  cout << "---------- BackwardSubsumptionAndResolution::perform ----------" << endl;
  CALL("BackwardSubsumptionAndResolution::perform");
  ASSERT_VALID(*cl);
  ASS(_index);
  simplifications = BwSimplificationRecordIterator::getEmpty();

  if(!_subsumption && !_subsumptionResolution) {
    return;
  }

  static DHSet<Clause *> checkedClauses;
  checkedClauses.reset();

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
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
        cout << "Subsumption: " << *cl << " subsumes " << *icl << endl;
        checkedClauses.insert(icl);
      }
    }
    // Check for subsumption resolution
    if (_subsumptionResolution) {
      SLQueryResultIterator rit = _index->getInstances(lit, true, false);
      while (rit.hasNext()) {
        SLQueryResult qr = rit.next();
        Clause *icl = qr.clause;
        if (checkedClauses.contains(icl)) {
          continue;
        }
        Clause *resCl = ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(icl, lit, cl);
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
        cout << "Subsumption resolution: " << *cl << " subsumes " << *icl << endl;
        checkedClauses.insert(icl);
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

  /********************************************************/
  /*      SUBSUMPTION AND RESOLUTION cl is NOT UNIT       */
  /********************************************************/
  if(!_subsumptionByUnitsOnly) {
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
        if (_subsumption && satSubs.checkSubsumptionResolution(cl, icl, _subsumptionResolution)) {
          cout << "Subsumption: " << *cl << " by " << *icl << endl;
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
        }
        else if (_subsumptionResolution) {
          // check subsumption resolution
          Clause *resCl = satSubs.checkSubsumptionResolution(cl, icl, _subsumption);
          if (resCl) {
            cout << "resCl: " << *resCl << endl;
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
          }
        }
      }
    }
  }

  if (!_subsumptionResolution ||  _srByUnitsOnly) {
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
      // check subsumption resolution
      Clause *resCl = satSubs.checkSubsumptionResolution(cl, icl, false);
      if (resCl) {
        cout << "resCl: " << *resCl << endl;
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, resCl), simplificationBuffer);
      }
    }
  }
  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
check_correctness:
  // The efficiency of this code is very terrible, but it is only used for debugging
  // Get the results from the old implementation
  DHSet<Clause*> checkedSimplifications;
  if(_subsumption) {
    BwSimplificationRecordIterator oldSimplifications = BwSimplificationRecordIterator::getEmpty();
    _slqbs.perform(cl, oldSimplifications);
    while(oldSimplifications.hasNext()) {
      BwSimplificationRecord rec = oldSimplifications.next();
      checkedSimplifications.insert(rec.toRemove);
      auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
      bool found = false;
      while(it.hasNext()) {
        BwSimplificationRecord rec2 = it.next();
        if(rec2.replacement == nullptr && rec2.toRemove == rec.toRemove) {
          found = true;
          break;
        }
      }
      if(!found) {
        cout << "------ FALSE POSITIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;
      }
    }
    auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
    while(it.hasNext()) {
      BwSimplificationRecord rec = it.next();
      if(rec.replacement == nullptr && !checkedSimplifications.contains(rec.toRemove)) {
        cout << "------ FALSE NEGATIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;
      }
    }
  }

  if(_subsumptionResolution) {
    BwSimplificationRecordIterator oldSimplifications = BwSimplificationRecordIterator::getEmpty();
    _bsr.perform(cl, oldSimplifications);
    while(oldSimplifications.hasNext()) {
      BwSimplificationRecord rec = oldSimplifications.next();
      checkedSimplifications.insert(rec.toRemove);
      auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
      bool found = false;
      while(it.hasNext()) {
        BwSimplificationRecord rec2 = it.next();
        if(rec2.replacement != nullptr && rec2.toRemove == rec.toRemove) {
          found = true;
          break;
        }
      }
      if(!found) {
        cout << "------ FALSE POSITIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;
        cout << "Resolution: " << rec.replacement->toNiceString() << endl;
      }
    }
    auto it = List<BwSimplificationRecord>::Iterator(simplificationBuffer);
    while(it.hasNext()) {
      BwSimplificationRecord rec = it.next();
      if(rec.replacement != nullptr && !checkedSimplifications.contains(rec.toRemove)) {
        cout << "------ FALSE NEGATIVE ------" << endl;
        cout << "Clause: " << *cl << endl;
        cout << "Subsumed: " << rec.toRemove->toNiceString() << endl;
        cout << "Resolution: " << rec.replacement->toNiceString() << endl;
      }
    }
  }

#endif
}

} // namespace Inferences
