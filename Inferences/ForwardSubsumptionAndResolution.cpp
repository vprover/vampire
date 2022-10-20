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

namespace Inferences {
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

#if VDEBUG
#define CHECK_SAT_SUBSUMPTION 1
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 1
#else
#define CHECK_SAT_SUBSUMPTION 0
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 0
#endif

#define NEW_VERSION_FORWARD 1

#define LOG_S_AND_R_INSTANCES 0
#if LOG_S_AND_R_INSTANCES
ofstream fileOut("subsumption_tried.txt");
#endif

#define USE_SMT_SUBSUMPTION 0

class SubsumptionLogger;

class FwSubsAndResStats {
public:
  std::unique_ptr<SubsumptionLogger> m_logger;
  int64_t m_logged_count = 0;    // count how many we would have logged even if there's no logger attached
  int64_t m_logged_count_sr = 0; // count how many we would have logged even if there's no logger attached

  // Store numDecisions as histogram
  // first two are originationg from subsumption
  // m_numDecisions_frequency[numDecisions] = absolute number of MLMatcher calls that return numDecisions
  vvector<int64_t> m_numDecisions_frequency;
  // only those where MLMatcher returned 'true'
  vvector<int64_t> m_numDecisions_successes;
  // same but for MLMatcher calls originating from SR
  vvector<int64_t> m_numDecisions_frequency_SR;
  vvector<int64_t> m_numDecisions_successes_SR;
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
#if USE_SMT_SUBSUMPTION
  env.out() << "\% Subsumption algorithm: smt3\n";
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
  out << "\% Subsumptions to be logged: " << fsstats.m_logged_count << "\n";
  out << "\% Subsumption Resolutions to be logged: " << fsstats.m_logged_count_sr << "\n";
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

#if NEW_VERSION_FORWARD == 1

bool ForwardSubsumptionAndResolution::checkSubsumption(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex)
{
  CALL("ForwardSubsumptionAndResolution::checkSubsumption");
  // Check unit clauses first
  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  ASS(cmStore.isEmpty());

  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      Clause *premise = rit.next().clause;
      if (ColorHelper::compatible(cl->color(), premise->color())) {
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        ASS_LE(premise->weight(), cl->weight());
#if CHECK_SAT_SUBSUMPTION
        subsumption_tried.push_back(SubsumptionInstance(premise, cl, true));
#endif
        // NOTE: we do not care about outputting the inference here, since this branch is not a target where we want to use SMT-Subsumption.
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
        fsstats.m_logged_count += 1;
        if (fsstats.m_logger) {
          fsstats.m_logger->logSubsumption(mcl, cl, false);
        }
        continue;
      }

      fsstats.m_logged_count += 1;
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
#if CHECK_SAT_SUBSUMPTION
        subsumption_tried.push_back(SubsumptionInstance(mcl, cl, true));
#endif
        return true;
      }
#if CHECK_SAT_SUBSUMPTION
      subsumption_tried.push_back(SubsumptionInstance(mcl, cl, false));
#endif
    }
  }
  return false;
}

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

  // This is subsumption resolution with unit clauses. We don't log these because we don't do smt-subsumption for these.
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
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
        if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
          subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
          alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
        }
#endif
        return resolutionClause;
      }
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
      if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
        subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
        alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
      }
#endif
      if (resolutionClause) {
        return resolutionClause;
      }
    }
    // Note that we only index the "least matchable" literal in the _fwIndex.
    // This performs SR when the indexed literal is in the subsumption part.
    {
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
          // if (checkForSubsumptionResolution(cl, cms, resLit, -1, li == 0) && ColorHelper::compatible(cl->color(), mcl->color())) {
          if (checkForSubsumptionResolution(cl, cms, resLit, li) && ColorHelper::compatible(cl->color(), mcl->color())) {
            resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
            ASS(resolutionClause);
            env.statistics->forwardSubsumptionResolution++;
            premises = pvi(getSingletonIterator(mcl));
          }
          if (resolutionClause) {
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
            if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
              subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
              alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
            }
#endif
            return resolutionClause;
          }
        }
        ASS_EQ(mcl->getAux<ClauseMatches>(), cms);
        mcl->setAux(nullptr);
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
        if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
          subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
          alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
        }
#endif
      }
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
          if (resolutionClause) {
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
            if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
              subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
              alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
            }
#endif
            return resolutionClause;
          }
        }
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
        if (alreadyAdded.find(pair<Clause *, Clause *>(mcl, cl)) == alreadyAdded.end()) {
          subsumptionResolution_tried.push_back(SubsumptionResolutionInstance(mcl, cl, resolutionClause));
          alreadyAdded.insert(pair<Clause *, Clause *>(mcl, cl));
        }
#endif
      }
    }
  }
  return nullptr;
}

bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");
  TIME_TRACE("forward subsumption");
  if (fsstats.m_logger) {
    fsstats.m_logger->logNextRound();
  }
#if CHECK_SAT_SUBSUMPTION || CHECK_SAT_SUBSUMPTION_RESOLUTION
  subsumption_tried.clear();
  subsumptionResolution_tried.clear();
#endif

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  bool result = false;

  Clause::requestAux();

  LiteralMiniIndex miniIndex(cl);
  #if CHECK_SAT_SUBSUMPTION
  #endif

  if (checkSubsumption(cl, premises, miniIndex)) {
    result = true;
  }
  else if (_subsumptionResolution && clen > 1) {
    Clause *solution = checkSubsumptionResolution(cl, premises, miniIndex);
    if (solution) {
      result = true;
      replacement = solution;
    }
  }
  Clause::releaseAux();
  // clear the stored matches
  while (cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }
#if CHECK_SAT_SUBSUMPTION

  for (SubsumptionInstance si : subsumption_tried) {
#if LOG_S_AND_R_INSTANCES
    fileOut << "S " << si._L->toString() << " " << si._M->toString() << " " << si._result << endl;
#endif
    bool expected = si._result;
    bool actual = smtsubs.checkSubsumption(si._L, si._M);
    if (expected != actual) {
      env.beginOutput();
      if (!expected) {
        env.out() << "------------- FALSE POSITIVE S  -------------" << endl;
      }
      else {
        env.out() << "------------- FALSE NEGATIVE S -------------" << endl;
      }
      env.out() << "Subsumption check missmatch: (" << expected << " != " << actual << ")" << endl;
      env.out() << "L: " << si._L->toString() << endl;
      env.out() << "M: " << si._M->toString() << endl;
      env.endOutput();
    }
  }
#endif
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
  for (SubsumptionResolutionInstance sir : subsumptionResolution_tried) {
#if LOG_S_AND_R_INSTANCES
    fileOut << "R " << sir._L->toString() << " " << sir._M->toString() << " " << (sir._conclusion != nullptr) << endl;
#endif
    Clause *expected = sir._conclusion;
    Clause *actual = smtsubs.checkSubsumptionResolution(sir._L, sir._M);
    if ((expected == nullptr) != (actual == nullptr)) {
      env.beginOutput();
      if (expected == nullptr) {
        env.out() << "------------- FALSE POSITIVE SR -------------" << endl;
      }
      else {
        env.out() << "------------- FALSE NEGATIVE SR-------------" << endl;
      }
      env.out() << "Subsumption resolution check missmatch:" << endl;
      env.out() << "L: " << sir._L->toString() << endl;
      env.out() << "M: " << sir._M->toString() << endl;
      if (expected) {
        env.out() << "Expected: " << expected->toString() << endl;
      }
      else {
        env.out() << "Expected: nullptr" << endl;
      }
      if (actual) {
        env.out() << "Actual: " << actual->toString() << endl;
      }
      else {
        env.out() << "Actual: nullptr" << endl;
      }
      env.endOutput();
    }
  }
#endif

  return result;
}

#else

bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");
  if (fsstats.m_logger) {
    fsstats.m_logger->logNextRound();
  }
#if CHECK_SMT_SUBSUMPTION || CHECK_SMT_SUBSUMPTION_RESOLUTION
  static vvector<Clause *> s_mcl_tried;
  s_mcl_tried.clear();
  static vvector<Clause *> sr_mcl_tried;
  sr_mcl_tried.clear();
  bool we_did_subsumption_resolution = false;
  bool fin_print_extra_info = false;
#endif

  Clause *resolutionClause = nullptr;

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  TIME_TRACE("forward subsumption");

  bool result = false;

  Clause::requestAux();

  static CMStack cmStore(64);
  ASS(cmStore.isEmpty());

  /*********************************************************************************
   * Subsumption by unit clauses
   ********************************************************************************/

  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      Clause *premise = rit.next().clause;
      if (ColorHelper::compatible(cl->color(), premise->color())) {
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        ASS_LE(premise->weight(), cl->weight());
        result = true;
#if CHECK_SMT_SUBSUMPTION
        s_mcl_tried.push_back(premise);
        // if (!smtsubs.checkSubsumption(premise, cl)) {
        //   std::cerr << "\% ***WRONG RESULT OF SMT-SUBSUMPTION***    UNIT expecting 1" << std::endl;
        //   std::cerr << "\% premise = " << premise->toString() << std::endl;
        //   std::cerr << "\% cl = " << cl->toString() << std::endl;
        // }
#endif
        // NOTE: we do not care about outputting the inference here, since this branch is not a target where we want to use SMT-Subsumption.
        goto fin;
      }
    }
  }

  /*********************************************************************************
   * Subsumption by long clauses
   ********************************************************************************/

  {
#if USE_SMT_SUBSUMPTION
    smtsubs.setupMainPremise(cl);
#else
    LiteralMiniIndex miniIndex(cl);
#endif

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

#if USE_SMT_SUBSUMPTION
        mcl->setAux(this);
        bool const isSubsumed = smtsubs.setupSubsumption(mcl) && smtsubs.solve() && ColorHelper::compatible(cl->color(), mcl->color());
#else
        ClauseMatches *cms = new ClauseMatches(mcl);
        mcl->setAux(cms);
        cmStore.push(cms);
        cms->fillInMatches(&miniIndex);

        if (cms->anyNonMatched()) {
          fsstats.m_logged_count += 1;
          if (fsstats.m_logger) {
            fsstats.m_logger->logSubsumption(mcl, cl, false);
          }
          continue;
        }

        fsstats.m_logged_count += 1;
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

#if CHECK_SMT_SUBSUMPTION
        s_mcl_tried.push_back(mcl);
        // if (smtsubs.checkSubsumption(mcl, cl) != isSubsumed) {
        //   std::cerr << "\% ***WRONG RESULT OF SMT-SUBSUMPTION***    MULTI expecting " << isSubsumed << std::endl;
        //   std::cerr << "\% mcl = " << mcl->toString() << std::endl;
        //   std::cerr << "\%  cl = " <<  cl->toString() << std::endl;
        // };
#endif
#endif

        if (isSubsumed) {
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          ASS_LE(mcl->weight(), cl->weight());
          result = true;
          goto fin;
        }
      }
    }

    /*********************************************************************************
     * Subsumption resolution
     ********************************************************************************/

    if (!_subsumptionResolution) {
      goto fin;
    }

    {
#if CHECK_SMT_SUBSUMPTION_RESOLUTION
      we_did_subsumption_resolution = true;
#endif
      // TimeCounter tc_fsr(TC_FORWARD_SUBSUMPTION_RESOLUTION);
      TIME_TRACE("forward subsumption resolution");

      // This is subsumption resolution with unit clauses. We don't log these because we don't do smt-subsumption for these.
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
            replacement = resolutionClause;
            result = true;
          }
#if CHECK_SMT_SUBSUMPTION_RESOLUTION
          sr_mcl_tried.push_back(mcl);
          // smtsubs.checkSubsumptionResolution(mcl, cl, resolutionClause);
#endif
          if (resolutionClause) {
            goto fin;
          }
        }
      }

#if USE_SMT_SUBSUMPTION
      ASS(cmStore.isEmpty());
#else
      // Note that we only index the "least matchable" literal in the _fwIndex.
      // This performs SR when the indexed literal is in the subsumption part.
      {
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
            // if (checkForSubsumptionResolution(cl, cms, resLit, -1, li == 0) && ColorHelper::compatible(cl->color(), mcl->color())) {
            if (checkForSubsumptionResolution(cl, cms, resLit, li) && ColorHelper::compatible(cl->color(), mcl->color())) {
              resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
              ASS(resolutionClause);
              env.statistics->forwardSubsumptionResolution++;
              premises = pvi(getSingletonIterator(mcl));
              replacement = resolutionClause;
              result = true;
            }
#if CHECK_SMT_SUBSUMPTION_RESOLUTION
            sr_mcl_tried.push_back(mcl);
            // NOTE: we can't do the check here because we might encounter the same clause again in the loop below (it's possible that we fail here but succeed later).
            // if (!smtsubs.checkSubsumptionResolution(cms->_cl, cl, resolutionClause)) {
            //   fin_print_extra_info = true;
            // }
#endif
            if (resolutionClause) {
              goto fin;
            }
          }
          ASS_EQ(mcl->getAux<ClauseMatches>(), cms);
          mcl->setAux(nullptr);
        }
      }
#endif

#if USE_SMT_SUBSUMPTION
      LiteralMiniIndex miniIndex(cl);
#endif

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
            replacement = resolutionClause;
            result = true;
          }
#if CHECK_SMT_SUBSUMPTION_RESOLUTION
          sr_mcl_tried.push_back(mcl);
          // // NOTE: we can't do the check here because we might encounter the same clause again in the loop with another resLit
          // if (!smtsubs.checkSubsumptionResolution(mcl, cl, resolutionClause)) {
          //   fin_print_extra_info = true;
          // }
#endif
          if (resolutionClause) {
            goto fin;
          }
        }
      }
    }
  }

fin:
  Clause::releaseAux();
  while (cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }
  {
#if CHECK_SAT_SUBSUMPTION

    for (SubsumptionInstance si : subsumption_tried) {
#if LOG_S_AND_R_INSTANCES
      fileOut << "S " << si._L->toString() << " " << si._M->toString() << " " << si._result << endl;
#endif
      bool expected = si._result;
      bool actual = smtsubs.checkSubsumption(si._L, si._M);
      if (expected != actual) {
        env.beginOutput();
        if (!expected) {
          env.out() << "------------- FALSE POSITIVE S  -------------" << endl;
        }
        else {
          env.out() << "------------- FALSE NEGATIVE S -------------" << endl;
        }
        env.out() << "Subsumption check missmatch: (" << expected << " != " << actual << ")" << endl;
        env.out() << "L: " << si._L->toString() << endl;
        env.out() << "M: " << si._M->toString() << endl;
        env.endOutput();
      }
    }
#endif
#if CHECK_SAT_SUBSUMPTION_RESOLUTION
    for (SubsumptionResolutionInstance sir : subsumptionResolution_tried) {
#if LOG_S_AND_R_INSTANCES
      fileOut << "R " << sir._L->toString() << " " << sir._M->toString() << " " << (sir._conclusion != nullptr) << endl;
#endif
      Clause *expected = sir._conclusion;
      Clause *actual = smtsubs.checkSubsumptionResolution(sir._L, sir._M);
      if ((expected == nullptr) != (actual == nullptr)) {
        env.beginOutput();
        if (expected == nullptr) {
          env.out() << "------------- FALSE POSITIVE SR -------------" << endl;
        }
        else {
          env.out() << "------------- FALSE NEGATIVE SR-------------" << endl;
        }
        env.out() << "Subsumption resolution check missmatch:" << endl;
        env.out() << "L: " << sir._L->toString() << endl;
        env.out() << "M: " << sir._M->toString() << endl;
        if (expected) {
          env.out() << "Expected: " << expected->toString() << endl;
        }
        else {
          env.out() << "Expected: nullptr" << endl;
        }
        if (actual) {
          env.out() << "Actual: " << actual->toString() << endl;
        }
        else {
          env.out() << "Actual: nullptr" << endl;
        }
        env.endOutput();
      }
    }
#endif
  }
  return result;
}
#endif

} // namespace Inferences
