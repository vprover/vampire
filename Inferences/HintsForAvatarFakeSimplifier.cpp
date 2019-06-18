
/*
 * File HintsForAvatarFakeSimplifier.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file HintsForAvatarFakeSimplifier.cpp
 * Implements class HintsForAvatarFakeSimplifier.
 */

#include "HintsForAvatarFakeSimplifier.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Matcher.hpp"

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

namespace Inferences
{

HintsForAvatarFwdFakeSimplifier::HintsForAvatarFwdFakeSimplifier() : _impl(false)
{
  CALL("HintsForAvatarFwdFakeSimplifier::HintsForAvatarFwdFakeSimplifier");

  // create indices for _impl and connect them with container!

  UnitClauseLiteralIndex* unitIdx =
      new UnitClauseLiteralIndex(new LiteralSubstitutionTree());

  FwSubsSimplifyingLiteralIndex* fwIdx =
      new FwSubsSimplifyingLiteralIndex(new LiteralSubstitutionTree());

  unitIdx->attachContainer(&_hintClauseContainer);
  fwIdx->attachContainer(&_hintClauseContainer);

  _impl.setIndices(unitIdx,fwIdx);
}

Clause* HintsForAvatarFwdFakeSimplifier::simplify(Clause* cl)
{
  CALL("HintsForAvatarFakeSimplifier::simplify");

  // cout << "HintsForAvatarFakeSimplifier::simplify" << endl;

  Clause* rDummy;
  Clause* pDummy;
  // never consider redundant, just mark as "hint-heeding"
  if (_impl.genericPerform(cl,rDummy,pDummy,TC_FORWARD_SUBSUMPTION_HINT_CHECK,TC_FORWARD_SUBSUMPTION_HINT_CHECK)) {
    cl->heedHint();
  }
  // always return cl; it's never actually simplified
  return cl;
}

HintsForAvatarBwdFakeSimplifier::HintsForAvatarBwdFakeSimplifier()
{
  CALL("HintsForAvatarBwdFakeSimplifier::HintsForAvatarBwdFakeSimplifier");

  _index = new SimplifyingLiteralIndex(new LiteralSubstitutionTree());
  _index->attachContainer(&_hintClauseContainer);
}

Clause* HintsForAvatarBwdFakeSimplifier::simplify(Clause* cl)
{
  CALL("HintsForAvatarBwdFakeSimplifier::simplify");

  // the following is copied and adapted from SLQueryBackwardSubsumption
  // (sharing the code seemed to awkward, as we are not interested in a list (or an iterator)
  // of the subsumed clauses, but just the existence of some

  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_HINT_CHECK);

  unsigned clen=cl->length();

  if(clen==0) {
    cl->heedHint(); // empty clauses are hint matching even if there are no hints
    return cl;
  }

  if(clen==1) {
    SLQueryResultIterator rit=_index->getInstances( (*cl)[0], false, false);

    if (rit.hasNext()) {
      cl->heedHint();
    }

    return cl;
  }

  unsigned lmIndex=0; //least matchable literal index
  unsigned lmVal=(*cl)[0]->weight();
  for(unsigned i=1;i<clen;i++) {
    Literal* curr=(*cl)[i];//-getTopLevelVars((*cl)[i]);
    unsigned currVal=curr->weight();
    if(currVal>lmVal) {
      lmIndex=i;
      lmVal=currVal;
    }
  }

  static DArray<LiteralList*> matchedLits(32);
  matchedLits.init(clen, 0);

  static DHSet<unsigned> basePreds;
  bool basePredsInit=false;
  bool mustPredInit=false;
  unsigned mustPred;

  static DHSet<Clause*> checkedClauses;
  checkedClauses.reset();

  SLQueryResultIterator rit = _index->getInstances((*cl)[lmIndex], false, false);
  while (rit.hasNext()) {
    SLQueryResult qr = rit.next();
    Clause* icl = qr.clause;
    Literal* ilit = qr.literal;
    unsigned ilen = icl->length();
    if (ilen < clen || icl == cl) {
      continue;
    }

    if (!checkedClauses.insert(icl)) {
      continue;
    }

    RSTAT_CTR_INC("H - bs1 0 candidates");

    //here we pick one literal header of the base clause and make sure that
    //every instance clause has it
    if (!mustPredInit) {
      //since the base clause has at least two children, this will always
      //contain an existing literal header after the loop
      mustPred = 0;
      for (unsigned bi = 0; bi < clen; bi++) {
        if (bi == lmIndex) {
          continue;
        }
        unsigned pred = (*cl)[bi]->header();
        if (pred > mustPred) {
          mustPred = pred;
        }
      }
    }
    bool haveMustPred = false;
    for (unsigned ii = 0; ii < ilen; ii++) {
      Literal* l = (*icl)[ii];
      if (l == ilit) {
        continue;
      }
      unsigned pred = l->header();
      if (pred == mustPred) {
        haveMustPred = true;
      }
    }
    if (!haveMustPred) {
      continue;
    }
    RSTAT_CTR_INC("H - bs1 1 mustPred survivors");

    //here we check that for every literal header in the base clause
    //there is a literal with the same header in the instance
    if (!basePredsInit) {
      basePredsInit = true;
      basePreds.reset();
      for (unsigned bi = 0; bi < clen; bi++) {
        if (bi == lmIndex) {
          continue;
        }
        unsigned pred = (*cl)[bi]->header();
        basePreds.insert(pred);
      }
    }
    unsigned allowedMisses = ilen - clen; //how many times the instance may contain a predicate that is not in the base clause
    bool fail = false;
    for (unsigned ii = 0; ii < ilen; ii++) {
      Literal* l = (*icl)[ii];
      if (l == ilit) {
        continue;
      }
      unsigned pred = l->header();
      if (!basePreds.find(pred)) {
        if (allowedMisses == 0) {
          fail = true;
          break;
        } else {
          allowedMisses--;
        }
      }
    }
    if (fail) {
      continue;
    }

    RSTAT_CTR_INC("H - bs1 2 survived");

    LiteralList::push(qr.literal, matchedLits[lmIndex]);
    for (unsigned bi = 0; bi < clen; bi++) {
      for (unsigned ii = 0; ii < ilen; ii++) {
        if (bi == lmIndex && (*icl)[ii] == qr.literal) {
          continue;
        }
        if (MatchingUtils::match((*cl)[bi], (*icl)[ii], false)) {
          LiteralList::push((*icl)[ii], matchedLits[bi]);
        }
      }
      if (!matchedLits[bi]) {
        goto match_fail;
      }
    }

    RSTAT_CTR_INC("H - bs1 3 final check");
    if (MLMatcher::canBeMatched(cl, icl, matchedLits.array(), 0)) {
      // mark successful hint match
      cl->heedHint();
      RSTAT_CTR_INC("H - bs1 4 performed");
    }

    // cleanup
    match_fail: for (unsigned bi = 0; bi < clen; bi++) {
      LiteralList::destroy(matchedLits[bi]);
      matchedLits[bi] = 0;
    }

    // stop early
    if (cl->heedingHint()) {
      break;
    }
  }

  // always return cl; it's never actually simplified
  return cl;
}


}
