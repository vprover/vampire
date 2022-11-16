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

#include <chrono>

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
#include "BackwardSubsumptionResolution.hpp"
#include "SLQueryBackwardSubsumption.hpp"
#endif

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace std::chrono;

/***************************************************************/
/*                     STATS COMPUTATION                       */
/***************************************************************/
class BwSRStats {
public:
  int64_t m_logged_count_s = 0;
  int64_t m_logged_success_s = 0;
  int64_t m_logged_count_sr = 0;
  int64_t m_logged_success_sr = 0;
  int64_t m_logged_useless_sat_checks_sr = 0;
  duration<int64_t, std::nano> m_time_on_perform = duration<int64_t, std::nano>::zero();
  duration<int64_t, std::nano> m_time_on_subsumption = duration<int64_t, std::nano>::zero();
  duration<int64_t, std::nano> m_time_on_resolution = duration<int64_t, std::nano>::zero();
  std::chrono::high_resolution_clock::time_point start_time_perform = high_resolution_clock::now();
  std::chrono::high_resolution_clock::time_point start_time_subsumption = high_resolution_clock::now();
  std::chrono::high_resolution_clock::time_point start_time_resolution = high_resolution_clock::now();

  bool started_perform = false;
  bool started_subsumption = false;
  bool started_resolution = false;

  void startPerform()
  {
    start_time_perform = high_resolution_clock::now();
    started_perform = true;
  }
  void startSubsumption()
  {
    start_time_subsumption = high_resolution_clock::now();
    started_subsumption = true;
  }
  void startResolution()
  {
    start_time_resolution = high_resolution_clock::now();
    started_resolution = true;
  }
  void stopPerform()
  {
    m_time_on_perform += high_resolution_clock::now() - start_time_perform;
    started_perform = false;
  }
  void stopSubsumption(bool success)
  {
    m_time_on_subsumption += high_resolution_clock::now() - start_time_subsumption;
    m_logged_count_s++;
    m_logged_success_s += success;
    started_subsumption = false;
  }
  void stopResolution(bool success)
  {
    m_time_on_resolution += high_resolution_clock::now() - start_time_resolution;
    m_logged_count_sr++;
    m_logged_success_sr += success;
    started_resolution = false;
  }
};

static BwSRStats bwStats;

void BackwardSubsumptionAndResolution::printStats(std::ostream &out)
{
  out << "**** Backward subsumption and resolution ****" << endl;
  out << "\% Total time on perform: " << ((double)bwStats.m_time_on_perform.count() / 1000000000) << " s\n";

  out << "\% Total time on subsumption: " << ((double)bwStats.m_time_on_subsumption.count() / 1000000000) << " s\n";
  out << "\% Subsumptions to be logged: " << bwStats.m_logged_count_s << "\n";
  out << "\% Subsumption Successes    : " << bwStats.m_logged_success_s << "\n\n";

  out << "\% Total time on subsumption resolution: " << ((double)bwStats.m_time_on_resolution.count() / 1000000000) << " s\n";
  out << "\% Subsumption Resolutions to be logged: " << bwStats.m_logged_count_sr << "\n";
  out << "\% Subsumption Resolution Successes    : " << bwStats.m_logged_success_sr << "\n";
  out << "\% Useless Subsumptions Resolution sat checks : " << bwStats.m_logged_useless_sat_checks_sr << "\n\n";

  if (bwStats.started_perform) {
    out << "Did not end perform" << endl;
  }
  if (bwStats.started_subsumption) {
    out << "Did not end subsumption" << endl;
  }
  if (bwStats.started_resolution) {
    out << "Did not end resolution" << endl;
  }
}

/***************************************************************/
/*                        CORE METHODS                         */
/***************************************************************/
void BackwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  CALL("BackwardSubsumptionAndResolution::attach");
  BackwardSimplificationEngine::attach(salg);
  _bwIndex = static_cast<BackwardSubsumptionIndex *>(
      _salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE));
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION || !USE_SAT_SUBSUMPTION_BACKWARD
  _slqbs.attach(salg);
  _bsr.attach(salg);
#endif
}

void BackwardSubsumptionAndResolution::detach()
{
  CALL("BackwardSubsumptionAndResolution::detach");
  _bwIndex = 0;
  _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION || !USE_SAT_SUBSUMPTION_BACKWARD
  _slqbs.detach();
  _bsr.detach();
#endif
  BackwardSimplificationEngine::detach();
}

#if !USE_SAT_SUBSUMPTION_BACKWARD
void BackwardSubsumptionAndResolution::perform(Clause *cl,
                                               BwSimplificationRecordIterator &simplifications)
{
  CALL("BackwardSubsumptionAndResolution::perform");
  bwStats.startPerform();
  ASSERT_VALID(*cl);
  ASS(_bwIndex);
  simplifications = BwSimplificationRecordIterator::getEmpty();

  List<BwSimplificationRecord> *simplificationBuffer = List<BwSimplificationRecord>::empty();

  static DHSet<Clause *> subsumed;
  subsumed.reset();

  if (_subsumption) {
    BwSimplificationRecordIterator subsumptions;
    bwStats.startSubsumption();
    _slqbs.perform(cl, subsumptions);
    bwStats.stopSubsumption(subsumptions.hasNext());
    while (subsumptions.hasNext()) {
      BwSimplificationRecord rec = subsumptions.next();
      subsumed.insert(rec.toRemove);
      List<BwSimplificationRecord>::push(rec, simplificationBuffer);
    }
  }

  if (_subsumptionResolution) {
    BwSimplificationRecordIterator resolutions;
    bwStats.startResolution();
    _bsr.perform(cl, resolutions);
    bwStats.stopResolution(resolutions.hasNext());
    while (resolutions.hasNext()) {
      BwSimplificationRecord rec = resolutions.next();
      if (!subsumed.contains(rec.toRemove)) {
        List<BwSimplificationRecord>::push(rec, simplificationBuffer);
      }
    }
  }
#else
void BackwardSubsumptionAndResolution::perform(Clause *cl,
                                               BwSimplificationRecordIterator &simplifications)
{
  CALL("BackwardSubsumptionAndResolution::perform");
  bwStats.startPerform();
  ASSERT_VALID(*cl);
  ASS(_bwIndex);
  simplifications = BwSimplificationRecordIterator::getEmpty();

  if (!_subsumption && !_subsumptionResolution) {
    bwStats.stopPerform();
    return;
  }

  _checked.reset();

  // The set of clauses that are subsumed by cl
  static DHSet<Clause *> subsumedSet;
  subsumedSet.reset();
  // contains the list of simplification found so far
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
        Clause *icl = it.next().clause;
        if (!_checked.insert(icl)) {
          continue;
        }
        bwStats.startSubsumption();
        subsumedSet.insert(icl);
        bwStats.stopSubsumption(true);
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
      }
    }
    if (_subsumptionResolution) {
      /***************************************************/
      /*      SUBSUMPTION RESOLUTION UNIT CLAUSE         */
      /***************************************************/
      auto it = _bwIndex->getInstances(lit, true, false);
      while (it.hasNext()) {
        Clause *icl = it.next().clause;
        if (subsumedSet.contains(icl) || !_checked.insert(icl)) {
          continue;
        }
        bwStats.startResolution();
        Clause *conclusion = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(icl, (*icl)[0], cl);
        bwStats.stopResolution(true);
        ASS(conclusion);
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
    goto check_correctness;
  }

  if (_subsumptionByUnitsOnly && _srByUnitsOnly) {
    ASS(!simplificationBuffer);
    goto check_correctness;
  }

#if SEPARATE_LOOPS_BACKWARD
  /*******************************************************/
  /*               SUBSUMPTION MULTI-LITERAL             */
  /*******************************************************/
  if (_subsumption && !_subsumptionByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the positively matched literals
      auto it = _bwIndex->getInstances(lit, false, false);
      while (it.hasNext()) {
        Clause *icl = it.next().clause;
        if (!_checked.insert(icl)) {
          continue;
        }
        // check subsumption and setup subsumption resolution at the same time
        bwStats.startSubsumption();
        if (satSubs.checkSubsumption(cl, icl, _subsumptionResolution)) {
          bwStats.stopSubsumption(true);
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
          subsumedSet.insert(icl);
        }
        else {
          bwStats.stopSubsumption(false);
        }
      }
    }
  }

  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  _checked.reset();
  if (_subsumptionResolution && !_srByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the negatively matched literals
      auto it = _bwIndex->getInstances(lit, true, false);
      while (it.hasNext()) {
        Clause *icl = it.next().clause;
        if (subsumedSet.contains(icl) || !_checked.insert(icl)) {
          continue;
        }

        // check subsumption resolution
        bwStats.startResolution();
        Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, false);
        bwStats.stopResolution(conclusion != nullptr);
        if (conclusion) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
        }
      }

      it = _bwIndex->getInstances(lit, false, false);
      while (it.hasNext()) {
        Clause *icl = it.next().clause;
        if (subsumedSet.contains(icl) || !_checked.insert(icl)) {
          continue;
        }

        // check subsumption resolution
        bwStats.startResolution();
        Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, false);
        bwStats.stopResolution(conclusion != nullptr);
        if (conclusion) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
        }
      }
    }
  }
#else
  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  if (!_subsumptionByUnitsOnly) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *lit = (*cl)[i];
      // find the positively matched literals
      auto it = _bwIndex->getInstances(lit, false, false);
      while (it.hasNext()) {
        Clause *icl = it.next().clause;
        if (!_checked.insert(icl)) {
          continue;
        }
        // check subsumption and setup subsumption resolution at the same time
        bool checkS = _subsumption && !_subsumptionByUnitsOnly;
        bool checkSR = _subsumptionResolution && !_srByUnitsOnly;
        if (checkS) {
          bwStats.startSubsumption();
          if (satSubs.checkSubsumption(cl, icl, checkSR)) {
            bwStats.stopSubsumption(true);
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
            subsumedSet.insert(icl);
            continue;
          }
          bwStats.stopSubsumption(false);
        }
        if (checkSR) {
          // check subsumption resolution
          bwStats.startResolution();
          Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, checkS); // use the previous setup only if subsumption was checked
          bwStats.stopResolution(conclusion != nullptr);
          if (conclusion) {
            List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
          }
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
        Clause *icl = it.next().clause;
        if (!_checked.insert(icl)) {
          continue;
        }
        // check subsumption resolution
        bwStats.startResolution();
        Clause *conclusion = satSubs.checkSubsumptionResolution(cl, icl, false);
        bwStats.stopResolution(conclusion != nullptr);
        if (conclusion) {
          List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
        }
      }
    }
  }
#endif

check_correctness:
  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }
  bwStats.stopPerform();

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
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

        if (_checked.contains(rec.toRemove)) {
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

        if (_checked.contains(rec.toRemove)) {
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
        if (_checked.contains(rec.toRemove)) {
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

        if (_checked.contains(rec.toRemove)) {
          cout << "Clause was checked" << endl;
        }
        else {
          cout << "Clause was NOT checked" << endl;
        }
      }
    }
  }

#endif
  return;
}
#endif

} // namespace Inferences
