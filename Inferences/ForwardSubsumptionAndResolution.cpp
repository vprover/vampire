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

#include "Lib/VirtualIterator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Timer.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include <fstream>
#include "Shell/TPTPPrinter.hpp"

#include "ForwardSubsumptionAndResolution.hpp"

#include <chrono>

namespace Inferences {
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace std::chrono;

#define CHAIN_RESOLUTION 1

#define LOG_S_AND_R_INSTANCES 0
#if LOG_S_AND_R_INSTANCES
ofstream fileOut("subsumption_tried.txt");
#endif

class SubsumptionLogger;

/***************************************************************/
/*                     STATS COMPUTATION                       */
/***************************************************************/
class FwSubsAndResStats {
public:
  std::unique_ptr<SubsumptionLogger> m_logger;
  int64_t m_logged_count_s = 0;
  int64_t m_logged_success_s = 0;
  int64_t m_logged_count_sr = 0;
  int64_t m_logged_success_sr = 0;
  int64_t m_logged_chained_sr = 0;
  int64_t m_logged_useless_sat_checks_sr = 0;
  duration<int64_t, std::nano> m_time_on_perform = duration<int64_t, std::nano>::zero();
  duration<int64_t, std::nano> m_time_on_subsumption = duration<int64_t, std::nano>::zero();
  duration<int64_t, std::nano> m_time_on_resolution = duration<int64_t, std::nano>::zero();
  std::chrono::_V2::system_clock::time_point start_time_perform = high_resolution_clock::now();
  std::chrono::_V2::system_clock::time_point start_time_subsumption = high_resolution_clock::now();
  std::chrono::_V2::system_clock::time_point start_time_resolution = high_resolution_clock::now();

  // Store numDecisions as histogram
  // first two are originating from subsumption
  // m_numDecisions_frequency[numDecisions] = absolute number of MLMatcher calls that return numDecisions
  vvector<int64_t> m_numDecisions_frequency;
  // only those where MLMatcher returned 'true'
  vvector<int64_t> m_numDecisions_successes;
  // same but for MLMatcher calls originating from SR
  vvector<int64_t> m_numDecisions_frequency_SR;
  vvector<int64_t> m_numDecisions_successes_SR;

  void startPerform() { start_time_perform = high_resolution_clock::now(); }
  void startSubsumption() { start_time_subsumption = high_resolution_clock::now(); }
  void startResolution() { start_time_resolution = high_resolution_clock::now(); }
  void stopPerform() { m_time_on_perform += high_resolution_clock::now() - start_time_perform; }
  void stopSubsumption(bool success)
  {
    m_time_on_subsumption += high_resolution_clock::now() - start_time_subsumption;
    m_logged_count_s++;
    m_logged_success_s += success;
  }
  void stopResolution(bool success)
  {
    m_time_on_resolution += high_resolution_clock::now() - start_time_resolution;
    m_logged_count_sr++;
    m_logged_success_sr += success;
  }
};

static FwSubsAndResStats fsstats;

ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution(bool subsumptionResolution)
    : _subsumptionResolution(subsumptionResolution)
{
  CALL("ForwardSubsumptionAndResolution::ForwardSubsumptionAndResolution");
  vstring const &logfile = env.options->subsumptionLogfile();
  if (!logfile.empty()) {
    BYPASSING_ALLOCATOR;
    fsstats.m_logger = make_unique<SubsumptionLogger>(logfile);
    // We cannot use the signal handler for termination if we want to log stuff properly
    Timer::setLimitEnforcement(false);
  }
}

ForwardSubsumptionAndResolution::~ForwardSubsumptionAndResolution()
{
  // if (fsstats.m_logger) {
  //   BYPASSING_ALLOCATOR;
  //   fsstats.m_logger.reset();
  // }
}

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  CALL("ForwardSubsumptionAndResolution::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
  env.beginOutput();
#if USE_SAT_SUBSUMPTION_FORWARD
  env.out() << "\% Subsumption algorithm: sat based\n";
#else
  env.out() << "\% Subsumption algorithm: original\n";
#endif
  env.endOutput();
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("ForwardSubsumptionAndResolution::detach");
  _unitIndex = 0;
  _fwIndex = 0;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

struct ClauseMatches {
  CLASS_NAME(ForwardSubsumptionAndResolution::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

private:
  // private and undefined operator= and copy constructor to avoid implicitly generated ones
  ClauseMatches(const ClauseMatches &);
  ClauseMatches &operator=(const ClauseMatches &);

public:
  ClauseMatches(Clause *cl) : _cl(cl), _zeroCnt(cl->length())
  {
    unsigned clen = _cl->length();
    _matches = static_cast<LiteralList **>(ALLOC_KNOWN(clen * sizeof(void *), "Inferences::ClauseMatches"));
    for (unsigned i = 0; i < clen; i++) {
      _matches[i] = 0;
    }
  }
  ~ClauseMatches()
  {
    unsigned clen = _cl->length();
    for (unsigned i = 0; i < clen; i++) {
      LiteralList::destroy(_matches[i]);
    }
    DEALLOC_KNOWN(_matches, clen * sizeof(void *), "Inferences::ClauseMatches");
  }

  void addMatch(Literal *baseLit, Literal *instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }
  void addMatch(unsigned bpos, Literal *instLit)
  {
    if (!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit, _matches[bpos]);
  }
  void fillInMatches(LiteralMiniIndex *miniIndex)
  {
    unsigned blen = _cl->length();

    for (unsigned bi = 0; bi < blen; bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while (instIt.hasNext()) {
        Literal *matched = instIt.next();
        addMatch(bi, matched);
      }
    }
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause *_cl;
  unsigned _zeroCnt;
  LiteralList **_matches;

  class ZeroMatchLiteralIterator {
  public:
    ZeroMatchLiteralIterator(ClauseMatches *cm)
        : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if (!cm->_zeroCnt) {
        _remaining = 0;
      }
    }
    bool hasNext()
    {
      while (_remaining > 0 && *_mlists) {
        _lits++;
        _mlists++;
        _remaining--;
      }
      return _remaining;
    }
    Literal *next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }

  private:
    Literal **_lits;
    LiteralList **_mlists;
    unsigned _remaining;
  };
};

typedef Stack<ClauseMatches *> CMStack;
static CMStack cmStore(64);

Clause *ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(Clause *cl, Literal *lit, Clause *baseClause)
{
  CALL("ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause");
  int clen = cl->length();
  int nlen = clen - 1;

  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, cl, baseClause));

  int next = 0;
  bool found = false;
  for (int i = 0; i < clen; i++) {
    Literal *curr = (*cl)[i];
    // As we will apply subsumption resolution after duplicate literal
    // deletion, the same literal should never occur twice.
    ASS(curr != lit || !found);
    if (curr != lit || found) {
      (*res)[next++] = curr;
    }
    else {
      found = true;
    }
  }

  return res;
}
class SubsumptionLogger {
private:
  std::ofstream m_file_slog;
  std::ofstream m_file_clauses;
  TPTPPrinter m_tptp;     // this needs to be a member so we get the type definitions only once at the beginning
  unsigned int m_seq = 1; // sequence number of logged inferences
  unsigned int m_last_side_premise = -1;
  unsigned int m_last_main_premise = -1;
  int m_last_reslitidx = -1;
  bool m_new_round = true;
  DHMap<unsigned int, vvector<Literal *>> m_logged_clauses;

public:
  CLASS_NAME(SubsumptionLogger);
  USE_ALLOCATOR(SubsumptionLogger);
  SubsumptionLogger(vstring logfile_path);
  void logNextRound();
  // Only log the clauses; must call logS... afterwards or the file will not be formatted correctly!
  // resLitIdx only matters for SR, value < 0 means "all".
  void logClauses(Clause *side_premise, Clause *main_premise, int resLitIdx);
  void logSubsumption(int result);
  void logSubsumptionResolution(int result);
  // convenience function
  void logSubsumption(Clause *side_premise, Clause *main_premise, int result);
  void logSubsumptionResolution(Clause *side_premise, Clause *main_premise, int resLitIdx, int result);
  void flush()
  {
    m_file_slog.flush();
    m_file_clauses.flush();
  }
};

SubsumptionLogger::SubsumptionLogger(vstring logfile_path)
    : m_file_slog{}, m_file_clauses{}, m_tptp{&m_file_clauses}
{
  CALL("SubsumptionLogger::SubsumptionLogger");
  vstring slog_path = logfile_path + ".slog";
  vstring clauses_path = logfile_path + ".p";
  m_file_slog.open(slog_path.c_str());
  m_file_clauses.open(clauses_path.c_str());
  ASS(m_file_slog.is_open());
  ASS(m_file_clauses.is_open());
}

void SubsumptionLogger::logNextRound()
{
  m_new_round = true;
}

void SubsumptionLogger::logClauses(Clause *side_premise, Clause *main_premise, int resLitIdx)
{
  // Print clauses if they haven't been printed yet
  for (Clause *clause : {side_premise, main_premise}) {
    if (!m_logged_clauses.find(clause->number())) {
      vvector<Literal *> literals;
      literals.reserve(clause->length());
      // NOTE: we store the order the literals are printed in.
      //       Because the clause may later be reordered due to literal selection.
      //       So we need to keep this data to preserve the correct resLitIdx.
      for (unsigned k = 0; k < clause->length(); ++k) {
        literals.push_back((*clause)[k]);
      }
      ASS_EQ(literals.size(), clause->length());
      m_logged_clauses.emplace(clause->number(), std::move(literals));
      // std::cerr << "printing " << clause << " " << clause->toString() << std::endl;
      vstringstream id_stream;
      id_stream << "clause_" << clause->number();
      m_tptp.printWithRole(id_stream.str(), "hypothesis", clause, false);
    }
  }
  m_last_main_premise = main_premise->number();
  m_last_side_premise = side_premise->number();
  if (resLitIdx >= 0) {
    // correct resLitIdx (required if clause has been reordered since printing)
    Literal *resLit = (*main_premise)[resLitIdx];
    vvector<Literal *> &lits = m_logged_clauses.get(main_premise->number());
    for (unsigned k = 0; k < lits.size(); ++k) {
      if (resLit == lits[k]) {
        resLitIdx = k;
        break;
      }
    }
  }
  m_last_reslitidx = resLitIdx;
  if (m_new_round) {
    m_file_slog << "R " << m_last_main_premise << '\n';
    m_new_round = false;
  }
}

void SubsumptionLogger::logSubsumption(int result)
{
  m_file_slog << "S " << m_last_side_premise << ' ' << result << '\n';
  m_seq += 1;
  m_last_main_premise = -1;
  m_last_side_premise = -1;
  m_last_reslitidx = -1;
}

void SubsumptionLogger::logSubsumptionResolution(int result)
{
  m_file_slog << "SR " << m_last_side_premise;
  if (m_last_reslitidx < 0) {
    m_file_slog << " *";
  }
  else {
    m_file_slog << ' ' << m_last_reslitidx;
  }
  m_file_slog << ' ' << result << '\n';
  m_seq += 1;
  m_last_main_premise = -1;
  m_last_side_premise = -1;
  m_last_reslitidx = -1;
}

void SubsumptionLogger::logSubsumption(Clause *side_premise, Clause *main_premise, int result)
{
  logClauses(side_premise, main_premise, -1);
  logSubsumption(result);
}

void SubsumptionLogger::logSubsumptionResolution(Clause *side_premise, Clause *main_premise, int resLitIdx, int result)
{
  logClauses(side_premise, main_premise, resLitIdx);
  logSubsumptionResolution(result);
}

void ForwardSubsumptionAndResolution::printStats(std::ostream &out)
{
  if (fsstats.m_logger) {
    fsstats.m_logger->flush();
    {
      BYPASSING_ALLOCATOR;
      fsstats.m_logger.reset();
    }
  }
  out << "**** Forward subsumption and resolution statistics ****" << endl;
  out << "\% Total time on perform: " << ((double)fsstats.m_time_on_perform.count() / 1000000000) << " s\n";

  out << "\% Total time on subsumption: " << ((double)fsstats.m_time_on_subsumption.count() / 1000000000) << " s\n";
  out << "\% Subsumptions to be logged: " << fsstats.m_logged_count_s << "\n";
  out << "\% Subsumption Successes    : " << fsstats.m_logged_success_s << "\n\n";

  out << "\% Total time on subsumption resolution: " << ((double)fsstats.m_time_on_resolution.count() / 1000000000) << " s\n";
  out << "\% Subsumption Resolutions to be logged: " << fsstats.m_logged_count_sr << "\n";
  out << "\% Subsumption Resolution Successes    : " << fsstats.m_logged_success_sr << "\n";
  out << "\% Useless Subsumptions Resolution sat checks : " << fsstats.m_logged_useless_sat_checks_sr << "\n\n";

  out << "\% Chained resolutions: " << fsstats.m_logged_chained_sr << "\n";
  out << "\% Subsumption MLMatcher Statistics\n\% (numDecisions Frequency Successes)\n";

  for (size_t n = 0; n < fsstats.m_numDecisions_frequency.size(); ++n) {
    if (fsstats.m_numDecisions_frequency[n] > 0) {
      out << "\% " << n << ' ' << fsstats.m_numDecisions_frequency[n] << ' ' << fsstats.m_numDecisions_successes[n] << '\n';
    }
  }
  out << "\% Subsumption Resolution MLMatcher Statistics\n\% (numDecisions Frequency Successes)\n";
  for (size_t n = 0; n < fsstats.m_numDecisions_frequency_SR.size(); ++n) {
    if (fsstats.m_numDecisions_frequency_SR[n] > 0) {
      out << "\% " << n << ' ' << fsstats.m_numDecisions_frequency_SR[n] << ' ' << fsstats.m_numDecisions_successes_SR[n] << '\n';
    }
  }
}

bool checkForSubsumptionResolution(Clause *cl, ClauseMatches *cms, Literal *resLit, int resLitIdx)
{
  bool should_log = true;
  ASS_GE(resLitIdx, 0);

  fsstats.m_logged_count_sr += 1;
  ASS_L(resLitIdx, (int)cl->length());
  if (resLitIdx >= 0) {
    ASS_EQ(resLit, (*cl)[resLitIdx]);
  }

  Clause *mcl = cms->_cl;
  unsigned mclen = mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if (zmli.hasNext()) {
    while (zmli.hasNext()) {
      Literal *bl = zmli.next();
      if (!MatchingUtils::match(bl, resLit, true)) {
        if (fsstats.m_logger && should_log) {
          fsstats.m_logger->logSubsumptionResolution(mcl, cl, resLitIdx, false);
        }
        return false;
      }
    }
  }
  else {
    bool anyResolvable = false;
    for (unsigned i = 0; i < mclen; i++) {
      if (MatchingUtils::match((*mcl)[i], resLit, true)) {
        anyResolvable = true;
        break;
      }
    }
    if (!anyResolvable) {
      if (fsstats.m_logger && should_log) {
        fsstats.m_logger->logSubsumptionResolution(mcl, cl, resLitIdx, false);
      }
      return false;
    }
  }

  if (fsstats.m_logger && should_log) {
    ASS_EQ(Timer::s_limitEnforcement, false);
    // we log the clauses first to make sure they haven't been deallocated yet (might happen due to weird code paths when exiting)
    // this is important because we want to catch subsumptions that cause vampire to time out! because these are the cases that the new algorithm should improve.
    fsstats.m_logger->logClauses(mcl, cl, resLitIdx);
    if (env.timeLimitReached()) {
      fsstats.m_logger->logSubsumptionResolution(-4);
      fsstats.m_logger->flush();
      throw TimeLimitExceededException();
    }
  }

  int isSR = -1;
  try {
    RSTAT_CTR_INC("MLSubsumptionResolution Calls");
    isSR = MLMatcher::canBeMatched(mcl, cl, cms->_matches, resLit);
  }
  catch (...) {
    std::cout << "BIG SUBSUMPTION RESOLUTION INTERRUPTED BY EXCEPTION!!! (time limit?)" << std::endl;
    if (fsstats.m_logger) {
      fsstats.m_logger->logSubsumptionResolution(-2);
      fsstats.m_logger->flush();
    }
    throw;
  }

  if (fsstats.m_logger && should_log) {
    fsstats.m_logger->logSubsumptionResolution(isSR);
    if (env.timeLimitReached()) {
      fsstats.m_logger->flush();
      throw TimeLimitExceededException();
    }
  }

  auto stats = MLMatcher::getStaticStats();
  if (stats.numDecisions >= fsstats.m_numDecisions_frequency_SR.size()) {
    size_t new_size = std::max(std::max(256ul, (size_t)stats.numDecisions + 1), fsstats.m_numDecisions_frequency_SR.size() * 2);
    fsstats.m_numDecisions_frequency_SR.resize(new_size, 0);
    fsstats.m_numDecisions_successes_SR.resize(new_size, 0);
  }
  fsstats.m_numDecisions_frequency_SR[stats.numDecisions] += 1;
  if (stats.result) {
    fsstats.m_numDecisions_successes_SR[stats.numDecisions] += 1;
  }

  return isSR;
}

#if CHECK_SAT_SUBSUMPTION || CHECK_SAT_SUBSUMPTION_RESOLUTION || !USE_SAT_SUBSUMPTION_FORWARD
/**
 * Checks whether there if @b cl is subsumed by any clause in the @b miniIndex.
 *
 * @param cl the clause to check for subsumption
 * @param premises the premise that successfully subsumed @b cl
 * @param miniIndex the index to check for subsumption
 * @return true if @b cl is subsumed by any clause in the @b miniIndex, false otherwise.
 */
bool ForwardSubsumptionAndResolution::checkSubsumption(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex)
{
  CALL("ForwardSubsumptionAndResolution::checkSubsumption");
  // Check unit clauses first
  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  ASS(cmStore.isEmpty());

  // check unit clauses
  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      Clause *premise = rit.next().clause;
      if (ColorHelper::compatible(cl->color(), premise->color())) {
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        ASS_LE(premise->weight(), cl->weight());
        // NOTE: we do not care about outputting the inference here, since this branch is not a target where we want to use sat-subsumption.
        return true;
      }
    }
  }

  // check long clauses
  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _fwIndex->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause *mcl = res.clause;
      if (mcl->hasAux()) {
        // we've already checked this clause
        continue;
      }
      ASS_G(mcl->length(), 1);

      // disable this for now (not done in master, needs to be checked and discussed)
      // if (mcl->length() > cl->length()) {
      //   RSTAT_CTR_INC("fw subsumption impossible due to length");
      // }

      ClauseMatches *cms = new ClauseMatches(mcl);
      mcl->setAux(cms);
      cmStore.push(cms);
      cms->fillInMatches(&miniIndex);

      if (cms->anyNonMatched()) {
        fsstats.m_logged_count_s += 1;
        if (fsstats.m_logger) {
          fsstats.m_logger->logSubsumption(mcl, cl, false);
        }
        continue;
      }

      fsstats.m_logged_count_s += 1;
      if (fsstats.m_logger) {
        ASS_EQ(Timer::s_limitEnforcement, false);
        // we log the clauses first to make sure they haven't been deallocated yet (might happen due to weird code paths when exiting)
        // this is important because we want to catch subsumptions that cause vampire to time out! because these are the cases that the new algorithm should improve.
        fsstats.m_logger->logClauses(mcl, cl, -1);
        if (env.timeLimitReached()) {
          fsstats.m_logger->logSubsumption(-4);
          fsstats.m_logger->flush();
          throw TimeLimitExceededException();
        }
      }
      int isSubsumed = -1;
      try {
        RSTAT_CTR_INC("MLSubsumption Calls");
        isSubsumed =
            MLMatcher::canBeMatched(mcl, cl, cms->_matches, 0) && ColorHelper::compatible(cl->color(), mcl->color());
      }
      catch (...) {
        std::cout << "BIG SUBSUMPTION INTERRUPTED BY EXCEPTION!!! (time limit?)" << std::endl;
        if (fsstats.m_logger) {
          fsstats.m_logger->logSubsumption(-2);
          fsstats.m_logger->flush();
        }
        throw;
      }

      if (fsstats.m_logger) {
        fsstats.m_logger->logSubsumption(isSubsumed);
        if (env.timeLimitReached()) {
          fsstats.m_logger->flush();
          throw TimeLimitExceededException();
        }
      }

      auto stats = MLMatcher::getStaticStats();
      if (stats.numDecisions >= fsstats.m_numDecisions_frequency.size()) {
        size_t new_size = std::max(std::max(256ul, (size_t)stats.numDecisions + 1), fsstats.m_numDecisions_frequency.size() * 2);
        fsstats.m_numDecisions_frequency.resize(new_size, 0);
        fsstats.m_numDecisions_successes.resize(new_size, 0);
      }
      fsstats.m_numDecisions_frequency[stats.numDecisions] += 1;
      if (stats.result) {
        fsstats.m_numDecisions_successes[stats.numDecisions] += 1;
      }

      if (isSubsumed) {
        premises = pvi(getSingletonIterator(mcl));
        env.statistics->forwardSubsumed++;
        ASS_LE(mcl->weight(), cl->weight());
        return true;
      }
    }
  }
  return false;
}

/**
 * Checks whether @b cl can be resolved then subsumed by any clause in the @b miniIndex.
 * If so, the resolution is returned.
 *
 * @param cl the clause to check for subsumption resolution
 * @param premises the premise that successfully resolved and subsumed @b cl
 * @param miniIndex the index to check for subsumption resolution
 * @return the conclusion of the resolution if @b cl can be resolved and subsumed, NULL otherwise
 */
Clause *ForwardSubsumptionAndResolution::checkSubsumptionResolution(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex)
{
  CALL("ForwardSubsumptionAndResolution::checkSubsumptionResolution");
  unsigned clen = cl->length();
  if (clen == 0) {
    return nullptr;
  }

  Clause *resolutionClause = nullptr;
  TIME_TRACE("forward subsumption resolution");
  vset<pair<Clause *, Clause *>> alreadyAdded;

  // This is subsumption resolution with unit clauses. We don't log these because we don't do sat-subsumption for these.
  for (unsigned li = 0; li < clen; li++) {
    Literal *resLit = (*cl)[li];
    SLQueryResultIterator rit = _unitIndex->getGeneralizations(resLit, true, false);
    while (rit.hasNext()) {
      Clause *mcl = rit.next().clause;
      ASS(!resolutionClause);
      if (ColorHelper::compatible(cl->color(), mcl->color())) {
        resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
        ASS(resolutionClause);
        env.statistics->forwardSubsumptionResolution++;
        premises = pvi(getSingletonIterator(mcl));
        return resolutionClause;
      }
      if (resolutionClause) {
        return resolutionClause;
      }
    }
  }
  // Note that we only index the "least matchable" literal in the _fwIndex.
  // This performs SR when the indexed literal is in the subsumption part.
  CMStack::Iterator csit(cmStore);
  while (csit.hasNext()) {
    ClauseMatches *cms = csit.next();
    Clause *mcl = cms->_cl;
    ASS_EQ(mcl->getAux<ClauseMatches>(), cms);
    for (unsigned li = 0; li < cl->length(); li++) {
      Literal *resLit = (*cl)[li];
      ASS(!resolutionClause);
      // only log the first occurrence with resLit *, because for these we always check all.
      // (actually not completely true if we encounter success... then we skip the remaining ones. and we can't replicate this behaviour during replay because of clause reordering)
      if (checkForSubsumptionResolution(cl, cms, resLit, li) && ColorHelper::compatible(cl->color(), mcl->color())) {
        resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
        ASS(resolutionClause);
        env.statistics->forwardSubsumptionResolution++;
        premises = pvi(getSingletonIterator(mcl));
      }
      if (resolutionClause) {
        return resolutionClause;
      }
    }
    ASS_EQ(mcl->getAux<ClauseMatches>(), cms);
    mcl->setAux(nullptr);
  }
  // This performs SR when the indexed literal is the resolved literal.

  for (unsigned li = 0; li < cl->length(); li++) {
    Literal *resLit = (*cl)[li]; // resolved literal
    SLQueryResultIterator rit = _fwIndex->getGeneralizations(resLit, true, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause *mcl = res.clause;

      // See https://github.com/vprover/vampire/pull/214
      ClauseMatches *cms = nullptr;
      if (mcl->hasAux()) {
        // We have seen the clause already, try to re-use the literal matches.
        // (Note that we can't just skip the clause: if our previous check
        // failed to detect subsumption resolution, it might still work out
        // with a different resolved literal.)
        cms = mcl->getAux<ClauseMatches>();
        // Already handled in the loop over cmStore above.
        if (!cms) {
          continue;
        }
      }
      if (!cms) {
        cms = new ClauseMatches(mcl);
        mcl->setAux(cms);
        cmStore.push(cms);
        cms->fillInMatches(&miniIndex);
      }
      ASS_EQ(mcl, cms->_cl);

      ASS(!resolutionClause);
      if (checkForSubsumptionResolution(cl, cms, resLit, li) && ColorHelper::compatible(cl->color(), mcl->color())) {
        resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
        ASS(resolutionClause);
        env.statistics->forwardSubsumptionResolution++;
        premises = pvi(getSingletonIterator(mcl));
      }
      if (resolutionClause) {
        return resolutionClause;
      }
    }
  }
  return nullptr;
}

#endif

#if !USE_SAT_SUBSUMPTION_FORWARD
/**
 * Checks whether the clause @b cl can be subsumed or resolved and subsumed by any clause is @b premises .
 * If the clause is subsumed, returns true
 * If the clause is resolved and subsumed, returns true and sets @b replacement to the conclusion clause
 * If the clause is not subsumed or resolved and subsumed, returns false
 *
 * @param cl the clause to check
 * @param replacement the replacement clause if the clause is resolved and subsumed
 * @param premises the premise that successfully subsumed or resolved and subsumed @b cl
 * @return true if the clause is subsumed or resolved and subsumed, false otherwise
 */
bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");
  TIME_TRACE("forward subsumption");
  fsstats.startPerform();
  if (fsstats.m_logger) {
    fsstats.m_logger->logNextRound();
  }

  unsigned clen = cl->length();
  if (clen == 0) {
    fsstats.stopPerform();
    return false;
  }

  bool result = false;

  Clause::requestAux();

  LiteralMiniIndex miniIndex(cl);

  fsstats.startSubsumption();
  if (checkSubsumption(cl, premises, miniIndex)) {
    fsstats.stopSubsumption(true);
    result = true;
  }
  else if (_subsumptionResolution) {
    fsstats.stopSubsumption(false);
    // Check for subsumption resolution
    fsstats.startResolution();
    replacement = checkSubsumptionResolution(cl, premises, miniIndex);
    fsstats.stopResolution(replacement != nullptr);
    if (replacement) {
      result = true;
    }
  }
  else {
    fsstats.stopSubsumption(false);
  }
  Clause::releaseAux();
  // clear the stored matches
  while (cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }

  fsstats.stopPerform();
  return result;
}

#endif

#if USE_SAT_SUBSUMPTION_FORWARD

#if CHAIN_RESOLUTION
/**
 * Creates a clause whose literals are the literals of @b cl except for the literal in @b litToExclude
 * @param cl the clause whose literals are to be copied
 * @param litToExclude the literal to exclude
 * @return the new clause
 *
 * @pre Assumes that the literals in @b litToExclude are in the same order as in cl
 */
static Clause *generateNSimplificationClause(Clause *cl, vvector<Literal *> litToExclude, Stack<Unit *> premises)
{
  CALL("generateNSimplificationClause");
  unsigned nlen = cl->length() - litToExclude.size();
  // convert premises into a list of units
  UnitList *premList = UnitList::singleton(cl);
  UnitList::pushFromIterator(Stack<Unit *>::Iterator(premises), premList);
  Clause *res = new (nlen) Clause(nlen,
                                  SimplifyingInferenceMany(InferenceRule::SUBSUMPTION_RESOLUTION, premList));
  unsigned j = 0;
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal *lit = (*cl)[i];
    if (j < litToExclude.size() && lit == litToExclude[j]) {
      j++;
      continue;
    }
    (*res)[i - j] = lit;
  }
  return res;
}
#endif

/**
 * Checks whether the clause @b cl can be subsumed or resolved and subsumed by any clause is @b premises .
 * If the clause is subsumed, returns true
 * If the clause is resolved and subsumed, returns true and sets @b replacement to the conclusion clause
 * If the clause is not subsumed or resolved and subsumed, returns false
 *
 * @param cl the clause to check
 * @param replacement the replacement clause if the clause is resolved and subsumed
 * @param premises the premise that successfully subsumed or resolved and subsumed @b cl
 * @return true if the clause is subsumed or resolved and subsumed, false otherwise
 */
bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");
  TIME_TRACE("forward subsumption");
  fsstats.startPerform();
  if (fsstats.m_logger) {
    fsstats.m_logger->logNextRound();
  }

  unsigned clen = cl->length();
  if (clen == 0) {
    fsstats.stopPerform();
    return false;
  }
  _subsumes = false;
  _conclusion = nullptr;
  _premise = nullptr;
  _checked.reset();

  Clause *mcl;

#if CHAIN_RESOLUTION
  static Stack<Unit *> premiseStack;
  premiseStack.reset();
  static vvector<Literal *> litToExclude;
  litToExclude.clear();
#endif

#if !SEPARATE_LOOPS_FORWARD
  // must be here to not mess up the goto with variable declarations
  unsigned n_sr_checks = 0;
#endif

  /*******************************************************/
  /*              SUBSUMPTION UNIT CLAUSE                */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption since
  // L = a where a is a single literal
  // M = b v C where sigma(a) = b is a given from the index
  // Therefore L subsumes M
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, false, false);
    if (it.hasNext()) {
      fsstats.startSubsumption();
      mcl = it.next().clause;
      _subsumes = true;
      _premise = mcl;
      fsstats.stopSubsumption(true);
      goto check_correctness;
    }
  }

#if SEPARATE_LOOPS_FORWARD
  /*******************************************************/
  /*               SUBSUMPTION MULTI-LITERAL             */
  /*******************************************************/
  // For each clauses mcl, check for subsumption
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      // if mcl is longer than cl, then it cannot subsume cl
      if (!_checked.insert(mcl)) {
        continue;
      }
      fsstats.startSubsumption();
      if (mcl->length() <= clen && satSubs.checkSubsumption(mcl, cl)) {
        fsstats.stopSubsumption(true);
        _subsumes = true;
        _premise = mcl;
        goto check_correctness;
      }
      fsstats.stopSubsumption(false);
    }
  }

  if (!_subsumptionResolution) {
    goto check_correctness;
  }

#else
  /*******************************************************/
  /*       SUBSUMPTION & RESOLUTION MULTI-LITERAL        */
  /*******************************************************/
  // For each clauses mcl, first check for subsumption, then for subsumption resolution
  // During subsumption, setup the subsumption resolution solver. This is an overhead
  // largely compensated because the success rate of subsumption is fairly low, and
  // in case of failure, having the solver ready is a great saving on subsumption resolution
  //
  // Since subsumption is stronger than subsumption, if a subsumption resolution check is found,
  // keep it until the end of the loop to make sure no subsumption is possible.
  // Only when it has been checked that subsumption is not possible does the conclusion of
  // subsumption resolution become relevant
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!_checked.insert(mcl)) {
        continue;
      }

      bool checkSR = _subsumptionResolution && !_conclusion;
      // if mcl is longer than cl, then it cannot subsume cl but still could be resolved
      bool checkS = mcl->length() <= clen;
      fsstats.startSubsumption();
      if (checkS && satSubs.checkSubsumption(mcl, cl, checkSR)) {
        _subsumes = true;
        _premise = mcl;
        fsstats.stopSubsumption(true);
        fsstats.m_logged_useless_sat_checks_sr += n_sr_checks;
        goto check_correctness;
      }
      else if (checkSR) {
        fsstats.stopSubsumption(false);
        // In this case, the literals come from the non complementary list, and there is therefore
        // a low chance of it being resolved. However, in the case where there is no negative match,
        // checkSubsumption resolution is very fast after subsumption, since filling the match set
        // for subsumption will have already detected that subsumption resolution is impossible
        n_sr_checks++;
        fsstats.startResolution();
        _conclusion = satSubs.checkSubsumptionResolution(mcl, cl, checkS);
        fsstats.stopResolution(_conclusion != nullptr);
        if (_conclusion) {
          ASS(_premise == nullptr);
          // cannot override the premise since the loop would have ended otherwise
          // the premise will be overriden if a subsumption is found
          _premise = mcl;
        }
      }
      else {
        fsstats.stopSubsumption(false);
      }
    }
  }

  if (_conclusion || !_subsumptionResolution) {
    goto check_correctness;
  }
#endif

  /*******************************************************/
  /*         SUBSUMPTION RESOLUTION UNIT CLAUSE          */
  /*******************************************************/
  // In case of unit clauses, no need to check subsumption resolution since
  // L = a where a is a single literal
  // M = ~b v C where sigma(a) = ~b is a given from the index
  // Therefore M can be replaced by C
  //
  // This behavior can be chained by enabling the CHAIN_RESOLUTION parameter
  // When CHAIN_RESOLUTION is true, the negatively matching literals are stacked
  // and removed at the same time
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _unitIndex->getGeneralizations(lit, true, false);
    if (it.hasNext()) {
      fsstats.startResolution();
      mcl = it.next().clause;
      // do it only once per literal
#if CHAIN_RESOLUTION
      premiseStack.push(mcl);
      litToExclude.push_back(lit);
#else
      _conclusion = generateSubsumptionResolutionClause(cl, lit, mcl);
      ASS(_conclusion != nullptr);
      _premise = mcl;
      break;
#endif
      fsstats.stopResolution(true);
    }
  }
#if CHAIN_RESOLUTION
  if (premiseStack.size() == 1) {
    _premise = (Clause *)premiseStack.pop();
    _conclusion = generateSubsumptionResolutionClause(cl, litToExclude[0], _premise);
    goto check_correctness;
  }
  else if (premiseStack.size() > 1) {
    fsstats.m_logged_chained_sr++;
    _conclusion = generateNSimplificationClause(cl, litToExclude, premiseStack);
    _premise = nullptr;
    goto check_correctness;
  }
#else
  if (_conclusion) {
    goto check_correctness;
  }
#endif

#if SEPARATE_LOOPS_FORWARD
  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  _checked.reset();
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().clause;

      if (!_checked.insert(mcl)) {
        continue;
      }

      fsstats.startResolution();
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      fsstats.stopResolution(_conclusion != nullptr);
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        goto check_correctness;
      }
    }
    it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;

      if (!_checked.insert(mcl)) {
        continue;
      }

      fsstats.startResolution();
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      fsstats.stopResolution(_conclusion != nullptr);
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        goto check_correctness;
      }
    }
  }
#else
  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  // Check for the last clauses that are negatively matched in th index.
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
      if (!_checked.insert(mcl)) {
        continue;
      }

      fsstats.startResolution();
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
      fsstats.stopResolution(_conclusion != nullptr);
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        goto check_correctness;
      }
    }
  }
#endif

check_correctness:

#if CHECK_SAT_SUBSUMPTION || CHECK_SAT_SUBSUMPTION_RESOLUTION
  LiteralMiniIndex miniIndex(cl);
  Clause::requestAux();
#endif

#if CHECK_SAT_SUBSUMPTION
  ClauseIterator premises_aux;
  if (_subsumes) {
    if (!checkSubsumption(cl, premises_aux, miniIndex)) {
      env.beginOutput();
      env.out() << "------------- FALSE POSITIVE S  -------------" << endl;
      env.out() << "L: " << _premise->toString() << endl;
      env.out() << "M: " << cl->toString() << endl;
      env.endOutput();
    }
  }
  else if (checkSubsumption(cl, premises_aux, miniIndex)) {
    env.beginOutput();
    env.out() << "------------- FALSE NEGATIVE S  -------------" << endl;
    env.out() << "L: " << cl->toString() << endl;
    Clause *mcl = premises_aux.next();
    env.out() << "M: " << mcl->toString() << endl;
    env.endOutput();
  }
#endif

#if CHECK_SAT_SUBSUMPTION_RESOLUTION
  if (!_subsumes && _subsumptionResolution) {
    if (!_conclusion) {
      ClauseIterator premises_aux;
      Clause *conclusion = checkSubsumptionResolution(cl, premises_aux, miniIndex);
      if (conclusion) {
        env.beginOutput();
        env.out() << "------------- FALSE NEGATIVE SR -------------" << endl;
        Clause *mcl = premises_aux.next();
        env.out() << "L: " << mcl->toString() << endl;
        env.out() << "M: " << cl->toString() << endl;
        env.out() << "Expected: " << conclusion->toString() << endl;
        env.out() << "Actual: nullptr" << endl;
        if (_checked.contains(mcl)) {
          env.out() << "M was checked" << endl;
        }
        else {
          env.out() << "M was not checked" << endl;
        }
        env.endOutput();
      }
    }
    else {
      ClauseIterator premises_aux;
      Clause *conclusion = checkSubsumptionResolution(cl, premises_aux, miniIndex);
      if (!conclusion) {
        env.beginOutput();
        env.out() << "------------- FALSE POSITIVE SR -------------" << endl;
        Clause *mcl = premises_aux.next();
        env.out() << "L: " << mcl->toString() << endl;
        env.out() << "M: " << cl->toString() << endl;
        env.out() << "Expected: nullptr" << endl;
        env.out() << "Actual: " << conclusion->toString() << endl;
        env.endOutput();
      }
    }
  }

#endif

#if CHECK_SAT_SUBSUMPTION || CHECK_SAT_SUBSUMPTION_RESOLUTION
  Clause::releaseAux();
  while (cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }
#endif

  if (_subsumes) {
    premises = pvi(getSingletonIterator(_premise));
    fsstats.m_time_on_perform += duration_cast<nanoseconds>(high_resolution_clock::now() - fsstats.start_time_perform);
    return true;
  }
  if (_conclusion) {
    replacement = _conclusion;
#if CHAIN_RESOLUTION
    if (!_premise) {
      ASS(premiseStack.size() > 1);
      ClauseList *premiseList = ClauseList::empty();
      for (unsigned i = 0; i < premiseStack.size(); i++) {
        ClauseList::push((Clause *)premiseStack[i], premiseList);
      }
      premises = pvi(ClauseList::Iterator(premiseList));
      fsstats.m_time_on_perform += duration_cast<nanoseconds>(high_resolution_clock::now() - fsstats.start_time_perform);
      return true;
    }
#endif
    premises = pvi(getSingletonIterator(_premise));
    fsstats.m_time_on_perform += duration_cast<nanoseconds>(high_resolution_clock::now() - fsstats.start_time_perform);
    return true;
  }
  fsstats.m_time_on_perform += duration_cast<nanoseconds>(high_resolution_clock::now() - fsstats.start_time_perform);
  return false;
}
#endif

} // namespace Inferences