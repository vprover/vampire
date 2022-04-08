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
#include "Lib/TimeCounter.hpp"

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

#include "ForwardSubsumptionAndResolution.hpp"

namespace Inferences {
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm *salg)
{
  CALL("ForwardSubsumptionAndResolution::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("ForwardSubsumptionAndResolution::detach");
  _unitIndex = 0;
  _fwIndex = 0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

struct ClauseMatches {
  CLASS_NAME(ForwardSubsumptionAndResolution::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
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
    //As we will apply subsumption resolution after duplicate literal
    //deletion, the same literal should never occur twice.
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

bool checkForSubsumptionResolution(Clause *cl, ClauseMatches *cms, Literal *resLit)
{
  Clause *mcl = cms->_cl;
  unsigned mclen = mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if (zmli.hasNext()) {
    while (zmli.hasNext()) {
      Literal *bl = zmli.next();
      //      if( !resLit->couldBeInstanceOf(bl, true) ) {
      if (!MatchingUtils::match(bl, resLit, true)) {
        return false;
      }
    }
  }
  else {
    bool anyResolvable = false;
    for (unsigned i = 0; i < mclen; i++) {
      //      if(resLit->couldBeInstanceOf((*mcl)[i], true)) {
      if (MatchingUtils::match((*mcl)[i], resLit, true)) {
        anyResolvable = true;
        break;
      }
    }
    if (!anyResolvable) {
      return false;
    }
  }

  return MLMatcher::canBeMatched(mcl, cl, cms->_matches, resLit);
}

bool ForwardSubsumptionAndResolution::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");

  Clause *resolutionClause = 0;

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  TimeCounter tc_fs(TC_FORWARD_SUBSUMPTION);

  bool result = false;

  Clause::requestAux();

  static CMStack cmStore(64);
  ASS(cmStore.isEmpty());

  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _unitIndex->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      Clause *premise = rit.next().clause;
      if (ColorHelper::compatible(cl->color(), premise->color())) {
        premises = pvi(getSingletonIterator(premise));
        env.statistics->forwardSubsumed++;
        result = true;
        goto fin;
      }
    }
  }

  {
    LiteralMiniIndex miniIndex(cl);

    for (unsigned li = 0; li < clen; li++) {
      SLQueryResultIterator rit = _fwIndex->getGeneralizations((*cl)[li], false, false);
      while (rit.hasNext()) {
        SLQueryResult res = rit.next();
        Clause *mcl = res.clause;
        if (mcl->hasAux()) {
          //we've already checked this clause
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

        if (MLMatcher::canBeMatched(mcl, cl, cms->_matches, 0) && ColorHelper::compatible(cl->color(), mcl->color())) {
          premises = pvi(getSingletonIterator(mcl));
          env.statistics->forwardSubsumed++;
          result = true;
          goto fin;
        }
      }
    }

    tc_fs.stop();

    if (!_subsumptionResolution) {
      goto fin;
    }

    {
      TimeCounter tc_fsr(TC_FORWARD_SUBSUMPTION_RESOLUTION);

      for (unsigned li = 0; li < clen; li++) {
        Literal *resLit = (*cl)[li];
        SLQueryResultIterator rit = _unitIndex->getGeneralizations(resLit, true, false);
        while (rit.hasNext()) {
          Clause *mcl = rit.next().clause;
          if (ColorHelper::compatible(cl->color(), mcl->color())) {
            resolutionClause = generateSubsumptionResolutionClause(cl, resLit, mcl);
            env.statistics->forwardSubsumptionResolution++;
            premises = pvi(getSingletonIterator(mcl));
            replacement = resolutionClause;
            result = true;
            goto fin;
          }
        }
      }

      {
        CMStack::Iterator csit(cmStore);
        while (csit.hasNext()) {
          ClauseMatches *cms = csit.next();
          for (unsigned li = 0; li < clen; li++) {
            Literal *resLit = (*cl)[li];
            if (checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color())) {
              resolutionClause = generateSubsumptionResolutionClause(cl, resLit, cms->_cl);
              env.statistics->forwardSubsumptionResolution++;
              premises = pvi(getSingletonIterator(cms->_cl));
              replacement = resolutionClause;
              result = true;
              goto fin;
            }
          }
          ASS_EQ(cms->_cl->getAux<ClauseMatches>(), cms);
          cms->_cl->setAux(nullptr);
        }
      }

      for (unsigned li = 0; li < clen; li++) {
        Literal *resLit = (*cl)[li]; //resolved literal
        SLQueryResultIterator rit = _fwIndex->getGeneralizations(resLit, true, false);
        while (rit.hasNext()) {
          SLQueryResult res = rit.next();
          Clause *mcl = res.clause;

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

          if (checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color())) {
            resolutionClause = generateSubsumptionResolutionClause(cl, resLit, cms->_cl);
            env.statistics->forwardSubsumptionResolution++;
            premises = pvi(getSingletonIterator(cms->_cl));
            replacement = resolutionClause;
            result = true;
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
  return result;
}

} // namespace Inferences
