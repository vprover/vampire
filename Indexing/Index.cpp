/**
 * @file Index.cpp
 * Implements class Index.
 *
 */

#include "../Kernel/Clause.hpp"

#include "LiteralIndexingStructure.hpp"

#include "Index.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

Index::~Index()
{
  while(_attachedContainers) {
    detachContainer(_attachedContainers->head());
  }
}

void Index::attachContainer(ClauseContainer* cc)
{
  SubscriptionData addedSD = cc->addedEvent.subscribe(this,&Index::onAddedToContainer);
  SubscriptionData removedSD = cc->removedEvent.subscribe(this,&Index::onRemovedFromContainer);

  ASS(!_attachedContainers->member(cc));
  ContainerList::push(cc,_attachedContainers);
  SDataList::push(addedSD, _subscriptionData);
  SDataList::push(removedSD, _subscriptionData);
}

void Index::detachContainer(ClauseContainer* cc)
{
  SubscriptionData removedSD = SDataList::pop(_subscriptionData);
  SubscriptionData addedSD = SDataList::pop(_subscriptionData);
  ASS(addedSD->belongsTo(cc->addedEvent));
  ASS(removedSD->belongsTo(cc->removedEvent));
  addedSD->unsubscribe();
  removedSD->unsubscribe();

  ASS(_attachedContainers->member(cc));
  _attachedContainers=_attachedContainers->remove(cc);
}

LiteralIndex::~LiteralIndex()
{
  delete _is;
}

SLQueryResultIterator LiteralIndex::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getUnifications(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getGeneralizations(lit, complementary, retrieveSubstitutions);
}

SLQueryResultIterator LiteralIndex::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  return _is->getInstances(lit, complementary, retrieveSubstitutions);
}


void GeneratingLiteralIndex::onAddedToContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    _is->insert((*c)[i], c);
  }
}

void GeneratingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    _is->remove((*c)[i], c);
  }
}

void SimplifyingLiteralIndex::onAddedToContainer(Clause* c)
{
  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    _is->insert((*c)[i], c);
  }
}

void SimplifyingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  unsigned clen=c->length();
  for(unsigned i=0; i<clen; i++) {
    _is->remove((*c)[i], c);
  }
}

void AtomicClauseSimplifyingLiteralIndex::onAddedToContainer(Clause* c)
{
  if(c->length()==1) {
    _is->insert((*c)[0], c);
  }
}

void AtomicClauseSimplifyingLiteralIndex::onRemovedFromContainer(Clause* c)
{
  if(c->length()==1) {
    _is->remove((*c)[0], c);
  }
}
