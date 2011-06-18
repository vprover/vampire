/**
 * @file Producer.cpp
 * Implements class Producer.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

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

  _urr = new URResolution(true, _lemmaIndex.ptr(), _ruleTailIndex.ptr());

  _unprocLemmaCont.setAgeWeightRatio(1,1);
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

    //TODO: add subsumption check

    Literal* lemmaLit = (*gen)[0];
    if(subsumedByLemma(lemmaLit)) {
      gen->destroyIfUnnecessary();
      RSTAT_CTR_INC("forward subsumed lemmas");
      continue;
    }

    LOG("P generated: "<<gen->toString());
    gen->setSelected(1);
    _alg.addLemma(gen);
//    cout<<lemmaLit->toString()<<endl;
  }
}

void Producer::addRule(Clause* rule)
{
  CALL("Producer::addRule");
  ASS(rule->length()>0);
  ASS_G(rule->selected(),0);
  ASS_GE(rule->selected(),rule->length()-1);

  //TODO: add subsumption check


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
//    cout<<head->toString()<<"\t"<<rule->toString()<<endl;
  }

  performURR(rule);
  _activeCont.add(rule);

  if(head) {
    _ruleHeadIndex->insert(head, rule);
  }
}

void Producer::removeRule(Clause* rule)
{
  CALL("Producer::removeRule");

  if(_toRemove.insert(rule)) {
    _rulesToRemove.push(rule);
  }
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
    _activeCont.remove(rule);
    if(rule->selected()==rule->length()-1) {
      Literal* head = (*rule)[rule->length()-1];
      _ruleHeadIndex->remove(head, rule);
    }
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

  SLQueryResultIterator rsrit = _ruleTailIndex->getInstances(lit, true, false);
  while(rsrit.hasNext()) {
    SLQueryResult slRec = rsrit.next();
    RSTAT_CTR_INC("chances for rule subsumption resolutions");
  }
}

void Producer::processLemma()
{
  CALL("Producer::processLemma");
  ASS(!_unprocLemmaCont.isEmpty());

  Clause* lemma = _unprocLemmaCont.popSelected();
  LOG("P processing lemma "<<lemma->toString());
  performURR(lemma);
  _activeCont.add(lemma);
}


}
