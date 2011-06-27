/**
 * @file Producer.cpp
 * Implements class Producer.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Shell/Options.hpp"

#include "TabulationAlgorithm.hpp"

#include "Producer.hpp"

#undef LOGGING
#define LOGGING 0

namespace Tabulation
{

void Producer::ActiveContainer::add(Clause* c)
{
  CALL("Producer::ActiveContainer::add");

  addedEvent.fire(c);
}

void Producer::ActiveContainer::remove(Clause* c)
{
  CALL("Producer::ActiveContainer::remove");

  removedEvent.fire(c);
}

Producer::Producer(TabulationAlgorithm& alg)
: _alg(alg)
{
  CALL("Producer::Producer");

  _unprocLemmaIndex = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
  _unprocLemmaIndex->attachContainer(&_unprocLemmaCont);

  _lemmaIndex = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
  _lemmaIndex->attachContainer(&_activeCont);

  _ruleTailIndex = new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree(), true);
  _ruleTailIndex->attachContainer(&_activeCont);

  _ruleHeadIndex = new LiteralSubstitutionTree();

  _ruleSubsumptionIndex = new CodeTreeSubsumptionIndex();
  _ruleSubsumptionIndex->attachContainer(&_activeCont);

  _ruleBwSubsumptionIndex = new SimplifyingLiteralIndex(new LiteralSubstitutionTree());
  _ruleBwSubsumptionIndex->attachContainer(&_activeCont);
  _bwSubsumptionRule = new SLQueryBackwardSubsumption(_ruleBwSubsumptionIndex.ptr(), false);

  _urr = new URResolution(true, _lemmaIndex.ptr(), _ruleTailIndex.ptr());

  _unprocLemmaCont.setAgeWeightRatio(
      env.options->tabulationLemmaAgeRatio(),env.options->tabulationLemmaWeightRatio());
}

bool Producer::subsumedByLemma(Literal* lit)
{
  CALL("Producer::subsumedByLemma");

  return _unprocLemmaIndex->getGeneralizations(lit, false, false).hasNext() ||
	_lemmaIndex->getGeneralizations(lit, false, false).hasNext();
}

void Producer::performURR(Clause* cl)
{
  CALL("Producer::performURR");

  ClauseIterator genIt = _urr->generateClauses(cl);
  while(genIt.hasNext()) {
    Clause* gen = genIt.next();
    if(gen->isEmpty()) {
      LOG("P refutation: "<<gen->toString());
      throw MainLoop::RefutationFoundException(gen);
    }
    ASS_EQ(gen->length(), 1);

    Literal* lemmaLit = (*gen)[0];
    if(subsumedByLemma(lemmaLit)) {
      gen->destroyIfUnnecessary();
      RSTAT_CTR_INC("forward subsumed lemmas");
      continue;
    }

    LOG("P generated: "<<gen->toString());
    gen->setSelected(1);
    newLemma(gen);
//    cout<<lemmaLit->toString()<<endl;
  }
}

bool Producer::isRuleForwardSubsumed(Clause* rule)
{
  CALL("Producer::isRuleForwardSubsumed");

  TimeCounter tc(TC_FORWARD_SUBSUMPTION);

  ClauseSResResultIterator rit = _ruleSubsumptionIndex->getSubsumingOrSResolvingClauses(rule, false);
  while(rit.hasNext()) {
    ClauseSResQueryResult qr = rit.next();
    RSTAT_CTR_INC("forward rule subsumption candidates");
    if(isRuleSubsumedBy(rule, qr.clause)) {
      RSTAT_CTR_INC("forward subsumed rules");
      return true;
    }
  }
  return false;
}

/**
 * This function should only be called on pairs returned by the clause subsumption index
 * (clause @c queryRule must be subsumed by clause @c subsumingRule). The only thing checked
 * is whether the corresponding rules are subsumed as well).
 */
bool Producer::isRuleSubsumedBy(Clause* candidateRule, Clause* subsumingRule)
{
  CALL("Producer::isRuleSubsumedBy");

  unsigned slen = subsumingRule->length();
  unsigned ssel = subsumingRule->selected();
  unsigned clen = candidateRule->length();
  unsigned csel = candidateRule->selected();

  if(csel==clen) {
    if(ssel==slen) {
      return true; //the precondition is that the two clauses in the argument subsume each other
    }
    else {
      ASS_EQ(ssel,slen-1);
      //rule without header (i.e. rule to derive refutation) cannot be subsumed by a rule that has header
      return false;
    }
  }
  ASS_EQ(csel,clen-1);

  static DArray<LiteralList*> alts;
  alts.init(slen, 0);

  if(ssel!=slen) {
    ASS_EQ(ssel,slen-1);
    Literal* shead = (*subsumingRule)[slen-1];
    Literal* chead = (*candidateRule)[clen-1];
    if(!MatchingUtils::match(shead, chead, false)) {
      return false;
    }
    LiteralList::push(chead, alts[slen-1]);
  }


  for(unsigned si=0; si<ssel; si++) {
    Literal* slit = (*subsumingRule)[si];
    for(unsigned ci=0; ci<csel; ci++) {
      Literal* clit = (*candidateRule)[ci];
      if(MatchingUtils::match(slit, clit, false)) {
	LiteralList::push(clit, alts[si]);
      }
    }
    if(!alts[si]) {
      return false;
    }
  }

  bool res = MLMatcher::canBeMatched(subsumingRule, candidateRule, alts.array(), 0);

  for(unsigned i=0; i<slen; i++) {
    if(alts[i]) {
      alts[i]->destroy();
      alts[i] = 0;
    }
  }

  return res;
}

void Producer::performRuleBackwardSubsumption(Clause* rule)
{
  CALL("Producer::performRuleBackwardSubsumption");

  BwSimplificationRecordIterator candIt;
  _bwSubsumptionRule->perform(rule, candIt);
  while(candIt.hasNext()) {
    BwSimplificationRecord rec = candIt.next();
    ASS(!rec.replacement);
    Clause* candidate = rec.toRemove;
    RSTAT_CTR_INC("backward rule subsumption candidates");
    if(isRuleSubsumedBy(candidate, rule)) {
      RSTAT_CTR_INC("backward rule subsumptions");
      removeRule(candidate);
    }
  }
}

void Producer::performRuleAddition(Clause* rule)
{
  CALL("Producer::performRuleAddition");
  ASS(rule->length()>0);
  ASS_G(rule->selected(),0);
  ASS_GE(rule->selected(),rule->length()-1);

  if(isRuleForwardSubsumed(rule)) {
    return;
  }


  LOG("P adding rule "<<rule->toString()<<" selected "<<rule->selected());

  Literal* head = 0;
  if(rule->selected()==rule->length()-1) {
    ASS_GE(rule->length(), 2);
    head = (*rule)[rule->length()-1];

    if(subsumedByLemma(head)) {
      LOG("P rule rejected by lemma "<<rule->toString());
      RSTAT_CTR_INC("rules subsumed by old lemmas");
      return;
    }
  }

  if(env.options->tabulationFwRuleSubsumptionResolutionByLemmas()) {
    rule = doForwardLemmaSubsumptionResolution(rule);
    if(!rule) {
      return;
    }
  }

  performRuleBackwardSubsumption(rule);


  rule->incRefCnt();
  performURR(rule);
  ASS_G(rule->selected(),0);
  _activeCont.add(rule);

  if(head) {
    _ruleHeadIndex->insert(head, rule);
  }
}

void Producer::addRule(Clause* rule)
{
  CALL("Producer::addRule");

  _rulesToAdd.push(rule);
}

void Producer::performRuleRemoval(Clause* rule)
{
  CALL("Producer::performRuleRemoval");

  _activeCont.remove(rule);
  if(rule->selected()==rule->length()-1) {
    Literal* head = (*rule)[rule->length()-1];
    _ruleHeadIndex->remove(head, rule);
  }
  rule->decRefCnt();
}

void Producer::removeRule(Clause* rule)
{
  CALL("Producer::removeRule");

  if(_toRemove.insert(rule)) {
    _rulesToRemove.push(rule);
  }
}

void Producer::newLemma(Clause* lemma)
{
  CALL("Producer::newLemma");

  _lemmasToAdd.push(lemma);
}

void Producer::removeLemma(Clause* lemma)
{
  CALL("Producer::removeLemma");

  if(_toRemove.insert(lemma)) {
    _lemmasToRemove.push(lemma);
  }
}

void Producer::onSafePoint()
{
  CALL("Producer::onSafePoint");

  while(_rulesToRemove.isNonEmpty()) {
    Clause* rule = _rulesToRemove.pop();
    performRuleRemoval(rule);
  }

  while(_lemmasToRemove.isNonEmpty()) {
    Clause* lemma = _lemmasToRemove.pop();
    if(!_unprocLemmaCont.remove(lemma)) {
      _activeCont.remove(lemma);
    }
  }
  if(!_toRemove.isEmpty()) {
    _toRemove.reset();
  }

  while(_lemmasToAdd.isNonEmpty()) {
    Clause* lemma = _lemmasToAdd.pop();
    _alg.addLemma(lemma);
  }

  while(_rulesToAdd.isNonEmpty()) {
    Clause* rule = _rulesToAdd.pop();
    performRuleAddition(rule);
  }
}

void Producer::onLemma(Clause* lemma)
{
  CALL("Producer::onLemma");
  ASS_EQ(lemma->length(), 1);

  _unprocLemmaCont.add(lemma);

  Literal* lit = (*lemma)[0];
  SLQueryResultIterator srit = _ruleHeadIndex->getInstances(lit,false, false);
  while(srit.hasNext()) {
    SLQueryResult srRec = srit.next();
    Clause* subsumedRule = srRec.clause;
    LOG("P rule subsumed: "<<subsumedRule->toString()<< " by "<<lit->toString());
    removeRule(subsumedRule);
    RSTAT_CTR_INC("rules subsumed by new lemmas");
  }

  SLQueryResultIterator slit = _lemmaIndex->getInstances(lit, false, false);
  while(slit.hasNext()) {
    SLQueryResult slRec = slit.next();
    Clause* subsumedLemma = slRec.clause;
    LOG("P lemma subsumed: "<<subsumedLemma->toString()<< " by "<<lit->toString());
    removeLemma(subsumedLemma);
    RSTAT_CTR_INC("backward subsumed lemmas");
  }

  if(env.options->tabulationBwRuleSubsumptionResolutionByLemmas()) {
    doBackwardLemmaSubsumptionResolution(lemma);
  }
}

void Producer::doBackwardLemmaSubsumptionResolution(Clause* lemma)
{
  CALL("Producer::doBackwardLemmaSubsumptionResolution");

  Literal* lit = (*lemma)[0];
  SLQueryResultIterator rsrit = _ruleTailIndex->getInstances(lit, true, false);
  while(rsrit.hasNext()) {
    SLQueryResult slRec = rsrit.next();
    Clause* tgt = slRec.clause;
    Clause* replacement = performLemmaSubsumptionResolution(tgt, lemma);
    removeRule(tgt);
    RSTAT_CTR_INC("rule backward subsumption resolutions by lemmas");
    if(replacement) { //otherwise rule became unit or refutation
      addRule(replacement);
    }
  }
}

Clause* Producer::doForwardLemmaSubsumptionResolution(Clause* rule)
{
  CALL("Producer::doForwardLemmaSubsumptionResolution");

  unsigned rsel = rule->selected();

  unsigned i = 0;
  while(i<rsel) {
    Literal* rlit = (*rule)[i];
    SLQueryResultIterator resIt = _unprocLemmaIndex->getGeneralizations(rlit, true, false);
    if(!resIt.hasNext()) {
      SLQueryResultIterator lit = _lemmaIndex->getGeneralizations(rlit, true, false);
    }
    if(!resIt.hasNext()) {
      i++;
      continue;
    }
    SLQueryResult res = resIt.next();
    Clause* lemma = res.clause;
    Clause* newRule = performLemmaSubsumptionResolution(rule, lemma);
    RSTAT_CTR_INC("rule forward subsumption resolutions by lemmas");
    if(!newRule) {
      return 0; //rule became either lemma or refutation
    }
    ASS_REP2(newRule->selected()<rsel, rule->toString(), newRule->toString());
    ASS_G(rule->length(),1);
    ASS_L(newRule->length(), rule->length());
    ASS(i==0 || (*newRule)[i-1]==(*rule)[i-1]); //the earlier literals don't change
    rule = newRule;
    rsel = rule->selected();
    ASS_GE(rsel,1);
  }
  return rule;
}

/**
 * Precondition: Some of rule's tail literals must be instance of the lemma.
 */
Clause* Producer::performLemmaSubsumptionResolution(Clause* tgtRule, Clause* lemma)
{
  CALL("Producer::performLemmaSubsumptionResolution");
  ASS_EQ(lemma->length(), 1);

  Literal* lemmaLit = (*lemma)[0];
  unsigned clen = tgtRule->length();
  unsigned csel = tgtRule->selected();

  static LiteralStack lits;
  lits.reset();

  for(unsigned i=0; i<csel; i++) {
    Literal* tlit = (*tgtRule)[i];
    if(!MatchingUtils::match(lemmaLit, tlit, true)) {
      lits.push(tlit);
    }
  }
  for(unsigned i=csel; i<clen; i++) {
    Literal* tlit = (*tgtRule)[i];
    lits.push(tlit);
  }
  ASS_L(lits.size(), clen);

  Clause* res = Clause::fromStack(lits,
      Unit::getInputType(tgtRule->inputType(), lemma->inputType()),
      new Inference2(Inference::SUBSUMPTION_RESOLUTION, tgtRule, lemma));
  res->setAge(tgtRule->age());
  unsigned headLen = clen-csel;
  ASS(headLen==0 || headLen==1);
  if(res->length()>1) {
    res->setSelected(res->length()-headLen);
    return res;
  }
  else if(res->length()==1) {
    res->setSelected(1);
    newLemma(res);
    return 0;
  }
  else {
    throw MainLoop::RefutationFoundException(res);
  }
}

void Producer::processLemma()
{
  CALL("Producer::processLemma");
  ASS(!_unprocLemmaCont.isEmpty());

  Clause* lemma = _unprocLemmaCont.popSelected();
  ASS_EQ(lemma->selected(),1);
  LOG("P processing lemma "<<lemma->toString());
  performURR(lemma);
  _activeCont.add(lemma);
}


}
