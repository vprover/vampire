/**
 * @file Producer.cpp
 * Implements class Producer.
 */

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "TabulationALgorithm.hpp"

#include "Producer.hpp"

namespace Tabulation
{

void Producer::LemmaContainer::add(Clause* c)
{
  CALL("Producer::LemmaContainer::add");

  addedEvent.fire(c);
}


Producer::Producer(TabulationAlgorithm& alg)
: _alg(alg)
{
  CALL("Producer::Producer");

  _lemmaIndex = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
  _lemmaIndex->attachContainer(&_lemmaCont);

  _ruleIndex = new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree(), true);
  _ruleIndex->attachContainer(&_ruleCont);

  _urr = new URResolution(true, _lemmaIndex.ptr(), _ruleIndex.ptr());
}

void Producer::performURR(Clause* cl)
{
  CALL("Producer::performURR");

  ClauseIterator genIt = _urr->generateClauses(cl);
  while(genIt.hasNext()) {
    Clause* gen = genIt.next();
    if(gen->isEmpty()) {
      throw MainLoop::RefutationFoundException(gen);
    }
    ASS_EQ(cl->length(), 1);

    //TODO: add subsumption check

    _alg.addLemma(cl);
  }
}

void Producer::addRule(Clause* rule)
{
  CALL("Producer::addRule");
  ASS(rule->length()>0);
  ASS_G(rule->selected(),0);
  ASS_GE(rule->selected(),rule->length()-1);

  //TODO: add subsumption check

  performURR(rule);
  _ruleCont.add(rule);
}

void Producer::onLemma(Clause* lemma)
{
  CALL("Producer::onLemma");
  ASS_EQ(lemma->length(), 1);

  _unprocLemmaCont.add(lemma);
}

void Producer::processLemma()
{
  CALL("Producer::processLemma");

  Clause* lemma = _unprocLemmaCont.popSelected();
  performURR(lemma);
  _lemmaCont.add(lemma);
}


}
