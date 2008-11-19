/**
 * @file Index.cpp
 * Implements class Index.
 *
 */

#include "Index.hpp"
#include "../Kernel/Clause.hpp"

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
  //void(Index::*addM)(Clause*) = ;
  //void(Index::*addM)(Clause*) = &this->onAddedToContainer;
  cc->addedEvent.subscribe(this,&Index::onAddedToContainer);
  cc->removedEvent.subscribe(this,&Index::onRemovedFromContainer);
  
  ASS(!_attachedContainers->member(cc));
  _attachedContainers=new ContainerList(cc,_attachedContainers);
}

void Index::detachContainer(ClauseContainer* cc)
{
  cc->addedEvent.unsubscribe(this,&Index::onAddedToContainer);
  cc->removedEvent.unsubscribe(this,&Index::onRemovedFromContainer);

  ASS(_attachedContainers->member(cc));
  _attachedContainers=_attachedContainers->remove(cc);
}

void Index::onAddedToContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    insert((*c)[i], c);
  }
}

void Index::onRemovedFromContainer(Clause* c)
{
  int selCnt=c->selected();
  for(int i=0; i<selCnt; i++) {
    remove((*c)[i], c);
  }
}
