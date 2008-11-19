/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "SaturationAlgorithm.hpp"

using namespace Saturation;


SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainer* passive)
: _imgr(this), _passive(passive)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();
}


SaturationAlgorithm::~SaturationAlgorithm()
{
  delete _unprocessed;
  delete _passive;
  delete _active;
}
