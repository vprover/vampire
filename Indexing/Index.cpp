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
 * @file Indexing/Index.cpp
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
  if(!_addedSD.isEmpty()) {
    ASS(!_removedSD.isEmpty());
    _addedSD->unsubscribe();
    _removedSD->unsubscribe();
  }
}

/**
 * Attaches index to a clause container
 *
 * Can only be called once per @b Index obejct lifetime.
 */
void Index::attachContainer(ClauseContainer* cc)
{
  ASS(_addedSD.isEmpty()); //only one container can be attached

  _addedSD = cc->addedEvent.subscribe(this,&Index::onAddedToContainer);
  _removedSD = cc->removedEvent.subscribe(this,&Index::onRemovedFromContainer);
}

}
