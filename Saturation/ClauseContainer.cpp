/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "ClauseContainer.hpp"

using namespace Saturation;

void ClauseContainer::addClauses(ClauseIterator cit)
{
  while(cit.hasNext()) {
    add(cit.next());
  }
}
