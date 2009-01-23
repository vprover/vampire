/**
 * @file Index.cpp
 * Implements class Index.
 *
 */

#include "Index.hpp"


namespace Indexing
{

using namespace Lib;
using namespace Kernel;
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

}
