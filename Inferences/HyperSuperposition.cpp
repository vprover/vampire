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
 * @file HyperSuperposition.cpp
 * Implements class HyperSuperposition.
 */

#include <algorithm>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BinaryResolution.hpp"
#include "EqualityResolution.hpp"

#include "HyperSuperposition.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void HyperSuperposition::attach(SaturationAlgorithm* salg)
{
  CALL("HyperSuperposition::attach");
  ASS(!_index);

//  GeneratingInferenceEngine::attach(salg);
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<UnitClauseLiteralIndex*> (
	  _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
}

void HyperSuperposition::detach()
{
  CALL("HyperSuperposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
//  GeneratingInferenceEngine::detach();
  ForwardSimplificationEngine::detach();
}

/**
 * Return true if weight of the first term is less for p1 than for p2.
 *
 * We use this to sort elements on the rewriter stack, so that larger rewrites get done first.
 */
bool HyperSuperposition::rewriterEntryComparator(RewriterEntry p1, RewriterEntry p2)
{
  CALL("HyperSuperposition::rewriterEntryComparator");

  unsigned w1 = p1.first.first.isVar() ? 1 : p1.first.first.term()->weight();
  unsigned w2 = p2.first.first.isVar() ? 1 : p2.first.first.term()->weight();

  return w1<w2;
}

bool HyperSuperposition::tryToUnifyTwoTermPairs(RobSubstitution& subst, TermList tp1t1, int bank11,
    TermList tp1t2, int bank12, TermList tp2t1, int bank21, TermList tp2t2, int bank22)
{
  CALL("HyperSuperposition::tryToUnifyTwoTermPairs");

  BacktrackData btData;
  subst.bdRecord(btData);

  if(!subst.unify(tp1t1, bank11, tp1t2, bank12)) {
    subst.bdDone();
    ASS(btData.isEmpty());
    return false;
  }
  if(!subst.unify(tp2t1, bank21, tp2t2, bank22)) {
    subst.bdDone();
    btData.backtrack();
    return false;
  }

  subst.bdDone();
  subst.bdCommit(btData);
  ASS(btData.isEmpty());
  return true;
}

bool HyperSuperposition::tryMakeTopUnifiableByRewriter(TermList t1, TermList t2, int t2Bank, int& nextAvailableBank, ClauseStack& premises,
      RewriterStack& rewriters, RobSubstitution& subst, Color& infClr)
{
  CALL("HyperSuperposition::tryGetTopRewriter");

  if(subst.unify(t1, 0, t2, t2Bank)) {
    return true;
  }

  TermList ut1 = subst.apply(t1, 0);
  TermList ut2 = subst.apply(t2, t2Bank);

  ASS(ut1.isTerm() || ut2.isTerm());

  TermList srt;
  if(ut1.isTerm()) {
    srt = SortHelper::getResultSort(ut1.term());
  }
  else {
    ASS(ut2.isTerm());
    srt = SortHelper::getResultSort(ut2.term());
  }
  Literal* queryEq = Literal::createEquality(true, ut1, ut2, srt);

  SLQueryResultIterator srqi = _index->getUnifications(queryEq, false, false);
  if(!srqi.hasNext()) {
    return false;
  }
  //for now we just get the first result
  SLQueryResult qr = srqi.next();
  Color clr = ColorHelper::combine(infClr, qr.clause->color());
  if(clr==COLOR_INVALID) {
    return false;
  }
  infClr = clr;

  Literal* rwrLit = qr.literal;

  TermList rwrT1 = *rwrLit->nthArgument(0);
  TermList rwrT2 = *rwrLit->nthArgument(1);

  int rwrBankIdx = nextAvailableBank++;
  if(!tryToUnifyTwoTermPairs(subst, t1, 0, rwrT1, rwrBankIdx, t2, t2Bank, rwrT2, rwrBankIdx)) {
    std::swap(rwrT1, rwrT2);
    ALWAYS(tryToUnifyTwoTermPairs(subst, t1, 0, rwrT1, rwrBankIdx, t2, t2Bank, rwrT2, rwrBankIdx));
  }

  rewriters.push(make_pair(TermPair(rwrT1,rwrT2), rwrBankIdx));
  premises.push(qr.clause);
  return true;
}

/**
 * the content of the reference arguments is undefined in case of failure
 */
bool HyperSuperposition::tryGetRewriters(Term* t1, Term* t2, int t2Bank, int& nextAvailableBank, ClauseStack& premises,
      RewriterStack& rewriters, RobSubstitution& subst, Color& infClr)
{
  CALL("HyperSuperposition::tryGetRewriters");
  ASS_EQ(t1->isLiteral(),t2->isLiteral());

//for this we'll need to handle some corner cases in rewriter application
//  if(!t1->isLiteral()) {
//    if(tryMakeTopUnifiableByRewriter(TermList(t1), TermList(t2), t2Bank, nextAvailableBank, premises, rewriters, subst, infClr)) {
//      return true;
//    }
//  }
  if(t1->functor()!=t2->functor()) {
    return false;
  }

  SubtermIterator t1it(t1);
  SubtermIterator t2it(t2);
  while(t1it.hasNext()) {
    ALWAYS(t2it.hasNext());
    TermList st1 = t1it.next();
    TermList st2 = t2it.next();
    if(tryMakeTopUnifiableByRewriter(st1, st2, t2Bank, nextAvailableBank, premises, rewriters, subst, infClr)) {
      t1it.right();
      t2it.right();
      continue;
    }
    if(!TermList::sameTopFunctor(st1, st2)) {
      return false;
    }
  }
  ASS(!t2it.hasNext());
  return true;
}

/**
 * Determine which terms need to be made equal to make terms/literals
 * t1 and t2 unify, try to find unit equalities that would unify these two terms
 * and if successful, apply the necessary substitution to clause @c cl and
 * the rewritings to t1 and this then to the literal at @c literalIndex. The
 * order of literals in the clause is preserved.
 *
 * If @c disjointVariables is true, the variables in t2 are considered to be disjoint
 * from variables of the clause and term t1.
 * Variables of t1 are always considered to conincide with variables of the clause.
 */
void HyperSuperposition::tryUnifyingSuperpositioins(Clause* cl, unsigned literalIndex, Term* t1, Term* t2,
    bool disjointVariables, ClauseStack& acc)
{
  CALL("HyperSuperposition::tryUnifyingSuperpositioins");

  ASS_EQ(t1->isLiteral(),t2->isLiteral());
  ASS(!t1->isLiteral() || t1->functor()==t2->functor());

  Color clauseClr = cl->color();

  static RobSubstitution subst;
  subst.reset();

  int bank2 = disjointVariables ? 1 : 0;
  int nextAvailBank = bank2+1;

  static ClauseStack premises;
  premises.reset();
  //the int is a variable bank index
  typedef pair<TermPair, int> RewriterEntry;
  typedef Stack<RewriterEntry> RewriterStack;
  static RewriterStack rewriters;
  rewriters.reset();

  if(!tryGetRewriters(t1, t2, bank2, nextAvailBank, premises, rewriters, subst, clauseClr)) {
    //we couldn't get the rewriters
    return;
  }

  if(rewriters.isEmpty()) {
    //there is no need for rewriting
    return;
  }

  //we need to process heavier terms first, so we don't change some subterms of
  //later terms during rewriting (thus making the rewriting impossible)
  std::sort(rewriters.begin(), rewriters.end(), rewriterEntryComparator);

  Term* t1Subst;
  if(t1->isLiteral()) {
    t1Subst = subst.apply(static_cast<Literal*>(t1),0);
  }
  else {
    t1Subst = subst.apply(TermList(t1), 0).term();
  }

  Term* t1Rwr = t1Subst;
  RewriterStack::TopFirstIterator rwrIt(rewriters);
  while(rwrIt.hasNext()) {
    RewriterEntry rwr = rwrIt.next();
    int rwrBank = rwr.second;
    TermList srcBase = rwr.first.first;
    TermList tgtBase = rwr.first.second;
    TermList src = subst.apply(srcBase, rwrBank);
    TermList tgt = subst.apply(tgtBase, rwrBank);
    t1Rwr = EqHelper::replace(t1Rwr, src, tgt);
  }

  static RobSubstitution checkerSubst;
  checkerSubst.reset();
  if(!checkerSubst.unifyArgs(t1Rwr, 0, t2, bank2)) {
    return;
  }

  static LiteralStack resLits;
  resLits.reset();

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit0 = (*cl)[i];
    if(i==literalIndex) {
      if(t1->isLiteral()) {
	ASS_EQ(lit0, t1);
	resLits.push(static_cast<Literal*>(t1Rwr));
      }
      else {
	Literal* lSubst = subst.apply(lit0, 0);
	Literal* lRwr = EqHelper::replace(lSubst, TermList(t1Subst), TermList(t1Rwr));
	resLits.push(lRwr);
      }
    }
    else {
      Literal* lSubst = subst.apply(lit0, 0);
      resLits.push(lSubst);
    }
  }

  UnitList* premLst = 0;
  UnitList::pushFromIterator(ClauseStack::Iterator(premises), premLst);
  UnitList::push(cl, premLst);

  Clause* res = Clause::fromStack(resLits, GeneratingInferenceMany(InferenceRule::HYPER_SUPERPOSITION_GENERATING, premLst));
  // MS: keeping the original semantics (GeneratingInferenceMany would compute max over all parents+1)
  res->setAge(cl->age()+1);

  RSTAT_CTR_INC("hyper-superposition");

  _salg->onNewClause(res);
  acc.push(res);
}

void HyperSuperposition::tryUnifyingNonequality(Clause* cl, unsigned literalIndex, ClausePairStack& acc)
{
  CALL("HyperSuperposition::tryUnifyingNonequality");

  Literal* lit = (*cl)[literalIndex];
  ASS(lit->isEquality());
  ASS(lit->isNegative());

  TermList t1 = *lit->nthArgument(0);
  TermList t2 = *lit->nthArgument(1);
  if(t1.isVar() || t2.isVar()) {
    //this unifies without any problems
    return;
  }

  static ClauseStack localRes;
  tryUnifyingSuperpositioins(cl, literalIndex, t1.term(), t2.term(), false, localRes);

  while(localRes.isNonEmpty()) {
    Clause* ocl = localRes.pop();
    Clause* resCl = EqualityResolution::tryResolveEquality(ocl, (*ocl)[literalIndex]);
    ASS(resCl);
    acc.push(ClausePair(ocl, resCl));
  }
}

Literal* HyperSuperposition::getUnifQueryLit(Literal* base)
{
  CALL("HyperSuperposition::getUnifQueryLit");

  unsigned arity = base->arity();
  static TermStack varArgs;
  for(unsigned i=varArgs.size(); i<arity; i++) {
    varArgs.push(TermList(i, false));
  }
  Literal* res = Literal::create(base, varArgs.begin());
  return res;
}

void HyperSuperposition::resolveFixedLiteral(Clause* cl, unsigned litIndex, ClausePairStack& acc)
{
  CALL("HyperSuperposition::resolveFixedLiteral");

  Literal* lit = (*cl)[litIndex];
  SLQueryResultIterator unifs = _index->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    SLQueryResult qr = unifs.next();
    Clause* genCl = BinaryResolution::generateClause(cl, lit, qr, getOptions());
    acc.push(ClausePair(cl, genCl));
  }
}

void HyperSuperposition::tryUnifyingToResolveWithUnit(Clause* cl, unsigned literalIndex, ClausePairStack& acc)
{
  CALL("HyperSuperposition::tryUnifyingToResolveWithUnit");

  Literal* lit = (*cl)[literalIndex];
  if(lit->isEquality()) {
    //now we don't bother with the argument normalization that is done in equalities
    return;
  }
  Literal* queryLit = getUnifQueryLit(lit);
  SLQueryResultIterator unifIt = _index->getUnifications(queryLit, true, false);

  static ClauseStack localRes;

  while(unifIt.hasNext()) {
    SLQueryResult unifRes = unifIt.next();
    localRes.reset();
    tryUnifyingSuperpositioins(cl, literalIndex, lit, unifRes.literal, true, localRes);
    while(localRes.isNonEmpty()) {
      Clause* resolvableCl = localRes.pop();
      resolveFixedLiteral(resolvableCl, literalIndex, acc);
    }
  }
}

/**
 * Interface for a generating inference
 */
ClauseIterator HyperSuperposition::generateClauses(Clause* cl)
{
  CALL("HyperSuperposition::generateClauses");

  TimeCounter tc(TC_HYPER_SUPERPOSITION);

  static ClausePairStack res;
  res.reset();

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    if(lit->isEquality() && lit->isNegative()) {
      tryUnifyingNonequality(cl, i, res);
    }
  }
  if(clen==1) {
    tryUnifyingToResolveWithUnit(cl, 0, res);
  }

  return getPersistentIterator(getMappingIterator(ClausePairStack::Iterator(res), SecondOfPairFn<ClausePair>()));
}


bool HyperSuperposition::tryGetUnifyingPremises(Term* t1, Term* t2, Color clr, bool disjointVariables, ClauseStack& premises)
{
  CALL("HyperSuperposition::tryGetUnifyingPremises");
  ASS_EQ(t1->isLiteral(),t2->isLiteral());
  ASS(!t1->isLiteral() || t1->functor()==t2->functor());

  Color clauseClr = clr;

  static RobSubstitution subst;
  subst.reset();

  int bank2 = disjointVariables ? 1 : 0;
  int nextAvailBank = bank2+1;

  static RewriterStack rewriters;
  rewriters.reset();

  return tryGetRewriters(t1, t2, bank2, nextAvailBank, premises, rewriters, subst, clauseClr);
}

Clause* HyperSuperposition::tryGetContradictionFromUnification(Clause* cl, Term* t1, Term* t2, bool disjointVariables,
    ClauseStack& premStack)
{
  CALL("HyperSuperposition::tryGetContradictionFromUnification");

  Color clr = cl->color();
  ClauseStack::Iterator cit(premStack);
  while(cit.hasNext()) {
    Clause* prem = cit.next();
    clr = ColorHelper::combine(clr, prem->color());
  }
  if(clr==COLOR_INVALID) {
    return 0;
  }
  if(!tryGetUnifyingPremises(t1, t2, clr, disjointVariables, premStack)) {
    return 0;
  }
  UnitList* premLst = 0;
  UnitList::pushFromIterator(ClauseStack::Iterator(premStack), premLst);
  UnitList::push(cl, premLst); 

  Clause* res = Clause::fromIterator(LiteralIterator::getEmpty(),
      GeneratingInferenceMany(InferenceRule::HYPER_SUPERPOSITION_SIMPLIFYING, premLst));
  // MS: keeping the original semantics (GeneratingInferenceMany would compute max over all parents+1)
  res->setAge(cl->age());
  return res;
}

bool HyperSuperposition::trySimplifyingFromUnification(Clause* cl, Term* t1, Term* t2, bool disjointVariables, ClauseStack& premStack,
    Clause*& replacement, ClauseIterator& premises)
{
  CALL("HyperSuperposition::trySimplifyingFromUnification");


  Clause* res = tryGetContradictionFromUnification(cl, t1, t2, false, premStack);
  if(!res) {
    return false;
  }

  ClauseStack::Iterator premIt(premStack);
  while(premIt.hasNext()) {
    Clause* pr = premIt.next();
    if(!ColorHelper::compatible(cl->color(), pr->color())) {
      return false;
    }
  }

  RSTAT_CTR_INC("hyper-superposition");

  replacement = res;
  premises = pvi(ClauseStack::Iterator(premStack));
  return true;
}

bool HyperSuperposition::tryUnifyingNonequalitySimpl(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("HyperSuperposition::tryUnifyingNonequalitySimpl");
  ASS_EQ(cl->length(), 1);

  Literal* lit = (*cl)[0];
  ASS(lit->isEquality());
  ASS(lit->isNegative());

  TermList t1 = *lit->nthArgument(0);
  TermList t2 = *lit->nthArgument(1);
  if(t1.isVar() || t2.isVar()) {
    //this unifies without any problems
    return false;
  }

  static ClauseStack premStack;
  premStack.reset();

  return trySimplifyingFromUnification(cl, t1.term(), t2.term(), false, premStack, replacement, premises);
}

bool HyperSuperposition::tryUnifyingToResolveSimpl(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("HyperSuperposition::tryUnifyingToResolveSimpl");
  ASS_EQ(cl->length(), 1);

  Literal* lit = (*cl)[0];
  if(lit->isEquality()) {
    //now we don't bother with the argument normalization that is done in equalities
    return false;
  }
  Literal* queryLit = getUnifQueryLit(lit);
  SLQueryResultIterator unifIt = _index->getUnifications(queryLit, true, false);

  static ClauseStack prems;

  while(unifIt.hasNext()) {
    SLQueryResult unifRes = unifIt.next();
    prems.reset();
    prems.push(unifRes.clause);

    if(trySimplifyingFromUnification(cl, lit, unifRes.literal, true, prems, replacement, premises)) {
      return true;
    }
  }
  return false;
}

/**
 * Interface for a fw simplifying inference
 */
bool HyperSuperposition::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("HyperSuperposition::perform");
  if(cl->length()!=1) {
    return false;
  }

  TimeCounter tc(TC_HYPER_SUPERPOSITION);

  Literal* lit = (*cl)[0];

  if(lit->isEquality() && lit->isNegative()) {
    if(tryUnifyingNonequalitySimpl(cl, replacement, premises)) {
      return true;
    }
  }
  return tryUnifyingToResolveSimpl(cl, replacement, premises);
}

}
