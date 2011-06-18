/**
 * @file Producer.cpp
 * Implements class Producer.
 */

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

  _ruleIndex = new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree(), true);
  _ruleIndex->attachContainer(&_activeCont);

  _ruleHeadIndex = new LiteralSubstitutionTree();

  _urr = new URResolution(true, _lemmaIndex.ptr(), _ruleIndex.ptr());

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
      continue;
    }

    LOG("P generated: "<<gen->toString());
    gen->setSelected(1);
    _alg.addLemma(gen);
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
      return;
    }
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

  _rulesToRemove.push(rule);
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
  }
}

void Producer::processLemma()
{
  CALL("Producer::processLemma");

  Clause* lemma = _unprocLemmaCont.popSelected();
  LOG("P processing lemma "<<lemma->toString());
  performURR(lemma);
  _activeCont.add(lemma);
}


}
