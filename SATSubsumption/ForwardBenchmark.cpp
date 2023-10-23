#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "ForwardBenchmark.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

#if !USE_SAT_SUBSUMPTION_FORWARD
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Debug/RuntimeStatistics.hpp"
#include "Kernel/MLMatcher.hpp"
#endif

#if !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
#include "Debug/RuntimeStatistics.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/ColorHelper.hpp"
#endif

#if CORRELATE_LENGTH_TIME
#include <chrono>
#include <fstream>
#endif

namespace Inferences {
using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace SATSubsumption;
using namespace std::chrono;

ForwardBenchmark::ForwardBenchmark(bool subsumptionResolution)
    : _subsumptionResolution(subsumptionResolution)
{
}

ForwardBenchmark::~ForwardBenchmark()
{
}

#if CORRELATE_LENGTH_TIME
static ofstream correlationFile;
#endif

void ForwardBenchmark::attach(SaturationAlgorithm *salg)
{
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
#if CORRELATE_LENGTH_TIME
  BYPASSING_ALLOCATOR
  {
    vstring fileName = "BenchmarkResult/correlation_";
#if SAT_SR_IMPL == 1
    fileName += "sat_1_";
#elif SAT_SR_IMPL == 2
    fileName += "sat_2_";
#endif
    fileName += env.options->problemName() + ".csv";
    correlationFile.open(fileName.c_str());
    correlationFile << "len_mcl,len_cl,time" << endl;
  }
#endif
}

void ForwardBenchmark::detach()
{
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

#if !USE_SAT_SUBSUMPTION_FORWARD || !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
struct ClauseMatches {
  CLASS_NAME(ForwardBenchmark::ClauseMatches);
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

#endif

#if !USE_SAT_SUBSUMPTION_FORWARD
/**
 * Checks whether there if @b cl is subsumed by any clause in the @b miniIndex.
 *
 * @param cl the clause to check for subsumption
 * @param premises the premise that successfully subsumed @b cl
 * @param miniIndex the index to check for subsumption
 * @return true if @b cl is subsumed by any clause in the @b miniIndex, false otherwise.
 */
bool ForwardBenchmark::checkSubsumption(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex)
{
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
        continue;
      }

      int isSubsumed = -1;
      try {
        RSTAT_CTR_INC("MLSubsumption Calls");
        isSubsumed =
            MLMatcher::canBeMatched(mcl, cl, cms->_matches, 0) && ColorHelper::compatible(cl->color(), mcl->color());
      }
      catch (...) {
        std::cout << "BIG SUBSUMPTION INTERRUPTED BY EXCEPTION!!! (time limit?)" << std::endl;
        throw;
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
#elif !USE_OPTIMIZED_FORWARD
bool ForwardBenchmark::checkSubsumption(Clause *cl)
{
  unsigned clen = cl->length();
  Clause *mcl;
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
      mcl = it.next().clause;
      _subsumes = true;
      _premise = mcl;
      return true;
    }
  }

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
      if (mcl->length() <= clen && satSubs.checkSubsumption(mcl, cl)) {
        _subsumes = true;
        _premise = mcl;
        return true;
      }
    }
  }
  return false;
}
#endif

#if !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
static bool checkForSubsumptionResolution(Clause *cl, ClauseMatches *cms, Literal *resLit, int resLitIdx)
{
  ASS_GE(resLitIdx, 0);
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
      return false;
    }
  }

  int isSR = -1;
  try {
    RSTAT_CTR_INC("MLSubsumptionResolution Calls");
    isSR = MLMatcher::canBeMatched(mcl, cl, cms->_matches, resLit);
  }
  catch (...) {
    std::cout << "BIG SUBSUMPTION RESOLUTION INTERRUPTED BY EXCEPTION!!! (time limit?)" << std::endl;
    throw;
  }

  return isSR;
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
Clause *ForwardBenchmark::checkSubsumptionResolution(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex)
{
  unsigned clen = cl->length();
  if (clen == 0) {
    return nullptr;
  }

#if USE_SAT_SUBSUMPTION_FORWARD
  // Need to fill the cms as the subsumption procedure does do it
  ASS(cmStore.isEmpty());
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

      ClauseMatches *cms = new ClauseMatches(mcl);
      mcl->setAux(cms);
      cmStore.push(cms);
      cms->fillInMatches(&miniIndex);

      if (cms->anyNonMatched()) {
        continue;
      }
    }
  }
#endif

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
        resolutionClause = SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, resLit, mcl);
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
        resolutionClause = SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, resLit, mcl);
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
        resolutionClause = SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, resLit, mcl);
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
#else
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
#if !USE_OPTIMIZED_FORWARD
Clause *ForwardBenchmark::checkSubsumptionResolution(Clause *cl)
{
  static Stack<Unit *> premiseStack;
  premiseStack.reset();
  static vvector<Literal *> litToExclude;
  litToExclude.clear();

  unsigned clen = cl->length();
  if (clen == 0) {
    return nullptr;
  }
  Clause *mcl;
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
      mcl = it.next().clause;
      // do it only once per literal
      premiseStack.push(mcl);
      litToExclude.push_back(lit);
    }
  }
  if (premiseStack.size() == 1) {
    _premise = (Clause *)premiseStack.pop();
    _conclusion = SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, litToExclude[0], _premise);
    return _conclusion;
  }
  else if (premiseStack.size() > 1) {
    _conclusion = generateNSimplificationClause(cl, litToExclude, premiseStack);
    _premise = nullptr;
    return _conclusion;
  }

  /*******************************************************/
  /*        SUBSUMPTION RESOLUTION MULTI-LITERAL         */
  /*******************************************************/
  for (unsigned li = 0; li < clen; li++) {
    Literal *lit = (*cl)[li];
    auto it = _fwIndex->getGeneralizations(lit, false, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
#if CORRELATE_LENGTH_TIME
      satSubs.builtSatProblem = false;
#endif
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
#if CORRELATE_LENGTH_TIME
      if (satSubs.builtSatProblem) {
        auto duration = chrono::duration_cast<chrono::microseconds>(satSubs.stop - satSubs.start);
        correlationFile << mcl->length() << "," << cl->length() << "," << duration.count() << endl;
      }
#endif
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        return _conclusion;
      }
    }
    it = _fwIndex->getGeneralizations(lit, true, false);
    while (it.hasNext()) {
      mcl = it.next().clause;
#if CORRELATE_LENGTH_TIME
      satSubs.builtSatProblem = false;
#endif
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
#if CORRELATE_LENGTH_TIME
      if (satSubs.builtSatProblem) {
        auto duration = chrono::duration_cast<chrono::microseconds>(satSubs.stop - satSubs.start);
        correlationFile << mcl->length() << "," << cl->length() << "," << duration.count() << endl;
      }
#endif
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        return _conclusion;
      }
    }
  }
  return nullptr;
}
#endif
#endif

#if !USE_SAT_SUBSUMPTION_FORWARD && !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
// configuration 1
bool ForwardBenchmark::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  bool result = false;

  Clause::requestAux();

  LiteralMiniIndex miniIndex(cl);

  if (checkSubsumption(cl, premises, miniIndex)) {
    result = true;
  }
  else if (_subsumptionResolution) {
    // Check for subsumption resolution
    replacement = checkSubsumptionResolution(cl, premises, miniIndex);
    if (replacement) {
      result = true;
    }
  }
  Clause::releaseAux();
  // clear the stored matches
  while (cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }

  return result;
}
#elif USE_SAT_SUBSUMPTION_FORWARD && !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD                          // Configuration 2
bool ForwardBenchmark::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  bool result = false;

  LiteralMiniIndex miniIndex(cl);
  if (checkSubsumption(cl)) {
    premises = pvi(getSingletonIterator(_premise));
    return true;
  }
  else if (_subsumptionResolution) {
    Clause::requestAux();
    // Check for subsumption resolution
    replacement = checkSubsumptionResolution(cl, premises, miniIndex);
    if (replacement) {
      premises = pvi(getSingletonIterator(_premise));
      result = true;
    }
    Clause::releaseAux();
    // clear the stored matches
    while (cmStore.isNonEmpty()) {
      delete cmStore.pop();
    }
    return result;
  }
  return false;
}
#elif USE_SAT_SUBSUMPTION_FORWARD && USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD && !USE_OPTIMIZED_FORWARD // Configuration 3
bool ForwardBenchmark::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  LiteralMiniIndex miniIndex(cl);

  if (checkSubsumption(cl)) {
    premises = pvi(getSingletonIterator(_premise));
    return true;
  }
  else if (_subsumptionResolution) {
    // Check for subsumption resolution
    replacement = checkSubsumptionResolution(cl);
    if (replacement) {
      premises = pvi(getSingletonIterator(_premise));
      return true;
    }
  }

  return false;
}
#elif USE_OPTIMIZED_FORWARD
// Configuration 4
bool ForwardBenchmark::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  TIME_TRACE("forward subsumption");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }
  _subsumes = false;
  _conclusion = nullptr;
  _premise = nullptr;
  _checked.reset();

  Clause *mcl;

  static Stack<Unit *> premiseStack;
  premiseStack.reset();
  static vvector<Literal *> litToExclude;
  litToExclude.clear();

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
      mcl = it.next().clause;
      _subsumes = true;
      _premise = mcl;
      goto end_forward;
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
      if (checkS) {
        if (satSubs.checkSubsumption(mcl, cl, checkSR)) {
          _subsumes = true;
          _premise = mcl;
          goto end_forward;
        }
      }
      if (checkSR) {
        // In this case, the literals come from the non complementary list, and there is therefore
        // a low chance of it being resolved. However, in the case where there is no negative match,
        // checkSubsumption resolution is very fast after subsumption, since filling the match set
        // for subsumption will have already detected that subsumption resolution is impossible
#if CORRELATE_LENGTH_TIME
        satSubs.builtSatProblem = false;
#endif
        _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
#if CORRELATE_LENGTH_TIME
        if (satSubs.builtSatProblem) {
          auto duration = chrono::duration_cast<chrono::microseconds>(satSubs.stop - satSubs.start);
          correlationFile << mcl->length() << "," << cl->length() << "," << duration.count() << endl;
        }
#endif
        if (_conclusion) {
          ASS(_premise == nullptr);
          // cannot override the premise since the loop would have ended otherwise
          // the premise will be overriden if a subsumption is found
          _premise = mcl;
        }
      }
    }
  }

  if (_conclusion || !_subsumptionResolution) {
    goto end_forward;
  }

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
      mcl = it.next().clause;
      premiseStack.push(mcl);
      litToExclude.push_back(lit);
    }
  }
  if (premiseStack.size() == 1) {
    _premise = (Clause *)premiseStack.pop();
    _conclusion = SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(cl, litToExclude[0], _premise);
    goto end_forward;
  }
  else if (premiseStack.size() > 1) {
    _conclusion = generateNSimplificationClause(cl, litToExclude, premiseStack);
    _premise = nullptr;
    goto end_forward;
  }

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
#if CORRELATE_LENGTH_TIME
      satSubs.builtSatProblem = false;
#endif
      _conclusion = satSubs.checkSubsumptionResolution(mcl, cl);
#if CORRELATE_LENGTH_TIME
      if (satSubs.builtSatProblem) {
        auto duration = chrono::duration_cast<chrono::microseconds>(satSubs.stop - satSubs.start);
        correlationFile << mcl->length() << "," << cl->length() << "," << duration.count() << endl;
      }
#endif
      if (_conclusion) {
        ASS(_premise == nullptr);
        _premise = mcl;
        goto end_forward;
      }
    }
  }

/*******************************************************/
/*                   ANALYZE RESULT                    */
/*******************************************************/
end_forward:
  if (_subsumes) {
    // Simple subsumption, set the premise
    premises = pvi(getSingletonIterator(_premise));
    return true;
  }
  if (_conclusion) {
    // Subsumption resolution, set the conclusion
    replacement = _conclusion;
    if (!_premise) {
      // If premise is null, it means that the chained resolution was used
      ASS(premiseStack.size() > 1);
      ClauseList *premiseList = ClauseList::empty();
      for (unsigned i = 0; i < premiseStack.size(); i++) {
        ClauseList::push((Clause *)premiseStack[i], premiseList);
      }
      premises = pvi(ClauseList::Iterator(premiseList));
      return true;
    }
    premises = pvi(getSingletonIterator(_premise));
    return true;
  }
  return false;
}
#endif

} // namespace Inferences
