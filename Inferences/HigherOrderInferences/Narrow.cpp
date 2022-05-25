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
 * @file Narrow.cpp
 * Implements class Narrow.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/Signature.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Narrow.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void Narrow::attach(SaturationAlgorithm* salg)
{
  CALL("Narrow::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<NarrowingIndex*> (
    _salg->getIndexManager()->request(NARROWING_INDEX) );
}

void Narrow::detach()
{
  CALL("Narrow::detach");

  _index=0;
  _salg->getIndexManager()->release(NARROWING_INDEX);
  GeneratingInferenceEngine::detach();
}

struct Narrow::ApplicableNarrowsFn
{
  ApplicableNarrowsFn(NarrowingIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("Narrow::ApplicableRewritesFn()");

    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
  }
private:
  NarrowingIndex* _index;
};

struct Narrow::RewriteableSubtermsFn
{
  RewriteableSubtermsFn(Ordering& ord) : _ord(ord) {}

  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    CALL("Narrow::RewriteableSubtermsFn()");

    return pvi( pushPairIntoRightIterator(lit, 
                EqHelper::getNarrowableSubtermIterator(lit, _ord)) );
  }

private:
  Ordering& _ord;
};


struct Narrow::ResultFn
{
  ResultFn(Clause* cl, Narrow& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Narrow::ResultFn::operator()");
    
    TermQueryResult& qr = arg.second;
    return _parent.performNarrow(_cl, arg.first.first, arg.first.second, qr.term, 
                                 qr.literal, qr.substitution);
  }
private:
  Clause* _cl;
  Narrow& _parent;
};

ClauseIterator Narrow::generateClauses(Clause* premise)
{
  CALL("Narrow::generateClauses");

  //cout << "Narrow with " << premise->toString() << endl;

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getMapAndFlattenIterator(it1,RewriteableSubtermsFn(_salg->getOrdering()));
  auto it3 = getMapAndFlattenIterator(it2,ApplicableNarrowsFn(_index));

  //Perform  Narrow
  auto it4 = getMappingIterator(it3,ResultFn(premise, *this));

  auto it5 = getFilteredIterator(it4,NonzeroFn());

  return pvi( it5 );
}



/**
 * If Narrow should be performed, return result of the Narrow,
 * otherwise return 0.
 */
Clause* Narrow::performNarrow(
    Clause* nClause, Literal* nLiteral, TermList nTerm, 
    TermList combAxLhs, Literal* combAx, ResultSubstitutionSP subst)
{
  CALL("Narrow::performNarrow");
  // we want the rwClause and eqClause to be active
  ASS(nClause->store()==Clause::ACTIVE);
  ASS(nTerm.isTerm());
  //if(nClause->number() == 276){
    //cout << "performNarrow with " << nClause->toString() /*<< "\n and " << nLiteral->toString() << "\n and " << nTerm.toString()*/ << endl;
    //cout << "the term being narrowed " << nTerm.toString() << endl;
    //cout << "combAxLhs " << combAxLhs.toString() << endl;
  //}

  static TermStack args;
  TermList head;
  ApplicativeHelper::getHeadAndArgs(nTerm, head, args);
  ASS(head.isVar());

  TermList headLHS = ApplicativeHelper::getHead(combAxLhs);
  ASS(ApplicativeHelper::isComb(headLHS));
  Signature::Combinator comb = ApplicativeHelper::getComb(headLHS);
  unsigned argNum = args.size();

  //0 means unlimited
  bool incr = false;
  unsigned lim = env.options->maxXXNarrows();
  if(lim != 0){
    if(comb < Signature::I_COMB && argNum == 1){
      if(nClause->inference().xxNarrows() == lim){
        env.statistics->discardedNonRedundantClauses++;
        return 0;
      } else {
        incr = true;
      }
    }
  }

  unsigned cLen = nClause->length();
  TermList combAxRhs = EqHelper::getOtherEqualitySide(combAx, combAxLhs);

  Ordering& ordering = _salg->getOrdering();

  TermList combAxRhsS = subst->apply(combAxRhs, 1);
  Literal* nLiteralS = subst->apply(nLiteral, 0); //0 is query bank
  TermList nTermS = subst->apply(nTerm, 0);

  //cout << "Check ordering on " << tgtTermS.toString() << " and " << rwTermS.toString() << endl;

  TermList arg0=*nLiteralS->nthArgument(0);
  TermList arg1=*nLiteralS->nthArgument(1);

  if(!arg0.containsSubterm(nTermS)) {
    if(Ordering::isGorGEorE(ordering.getEqualityArgumentOrder(nLiteralS))) {
      return 0;
    }
  } else if(!arg1.containsSubterm(nTermS)) {
    if(Ordering::isGorGEorE(Ordering::reverse(ordering.getEqualityArgumentOrder(nLiteralS)))) {
      return 0;
    }
  }

  Literal* tgtLitS = EqHelper::replace(nLiteralS,nTermS,combAxRhsS);

  //TODO required?
  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  InferenceRule rule;
  if(comb == Signature::S_COMB && argNum == 1){
    rule = InferenceRule::SXX_NARROW;
  } else if(comb == Signature::S_COMB && argNum == 2){
    rule = InferenceRule::SX_NARROW;
  } else if(comb == Signature::S_COMB && argNum == 3){
    rule = InferenceRule::S_NARROW;
  } else if(comb == Signature::C_COMB && argNum == 1){
    rule = InferenceRule::CXX_NARROW;
  } else if(comb == Signature::C_COMB && argNum == 2){
    rule = InferenceRule::CX_NARROW;
  } else if(comb == Signature::C_COMB && argNum == 3){
    rule = InferenceRule::C_NARROW;
  } else if(comb == Signature::B_COMB && argNum == 1){
    rule = InferenceRule::BXX_NARROW;
  } else if(comb == Signature::B_COMB && argNum == 2){
    rule = InferenceRule::BX_NARROW;
  } else if(comb == Signature::B_COMB && argNum == 3){
    rule = InferenceRule::B_NARROW;
  } else if(comb == Signature::K_COMB && argNum == 1){
    rule = InferenceRule::KX_NARROW;
  } else if(comb == Signature::K_COMB && argNum == 2){
    rule = InferenceRule::K_NARROW;
  } else {
    rule = InferenceRule::I_NARROW;
  }

  Inference inf(GeneratingInference1(rule, nClause));
  if(incr){ inf.incXXNarrows(); }

  // If proof extra is on let's compute the positions we have performed
  // Narrow on 
  /*if(env.options->proofExtra()==Options::ProofExtra::FULL){
    
    inf->setExtra(extra);
  }*/ //TODO update proof extra

  bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();

  Clause* res = new(cLen) Clause(cLen, inf);

  (*res)[0] = tgtLitS;
  int next = 1;
  for(unsigned i=0;i<cLen;i++) {
    Literal* curr=(*nClause)[i];
    if(curr!=nLiteral) {
      Literal* currAfter = subst->apply(curr, 0);

      if(EqHelper::isEqTautology(currAfter)) {
        goto construction_fail;
      }

      if (afterCheck) {
        TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
        if (i < nClause->numSelected() && ordering.compare(currAfter,nLiteralS) == Ordering::GREATER) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          goto construction_fail;
        }
      }
      (*res)[next++] = currAfter;
    }
  }

  env.statistics->narrow++;
  return res;

construction_fail:
  //cout << "failed" << endl;
  res->destroy();
  return 0;
}
