/**
 * @file TabulationContainers.cpp
 * Implements class TabulationContainers.
 */

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "TabulationContainers.hpp"

namespace Tabulation
{

///////////////////////
// GIContainer
//

GIContainer::GIContainer()
{
  CALL("GIContainer::GIContainer");

  LiteralIndexingStructure* lis = new LiteralSubstitutionTree();
  _unifIndex = new GeneratingLiteralIndex(lis);
  _unifIndex->attachContainer(this);
}

void GIContainer::add(Clause* c)
{
  CALL("GIContainer::add");

  addedEvent.fire(c);
}

/////////////////////////
//// LTContainer
////
//
//LTContainer::LTContainer()
//{
//  CALL("LTContainer::LTContainer");
//
//  _resolution = new BinaryResolution(getIndex());
//}

/////////////////////////
// GoalLiteralContainer
//

GoalLiteralContainer::GoalLiteralContainer()
{
  CALL("GoalLiteralContainer::GoalLiteralContainer");

  //TODO: check literal code tree implementation and replace SubstitutionTree by CodeTree
  _index = new LiteralSubstitutionTree();
}

void GoalLiteralContainer::add(Literal* lit)
{
  CALL("GoalLiteralContainer::add");
  ASS(!isSubsumed(lit));

  _index->insert(lit, 0);
}

bool GoalLiteralContainer::isSubsumed(Literal* lit)
{
  CALL("GoalLiteralContainer::isSubsumed");

  return _index->getGeneralizations(lit, false, false).hasNext();
}


}
