/**
 * @file ForwardLiteralRewriting.cpp
 * Implements class ForwardLiteralRewriting.
 */

#include "ForwardLiteralRewriting.hpp"

namespace Inferences
{

void ForwardLiteralRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardLiteralRewriting::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE) );
}

void ForwardLiteralRewriting::detach()
{
  CALL("ForwardLiteralRewriting::detach");
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


void ForwardLiteralRewriting::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("ForwardLiteralRewriting::perform");

  //TODO: add time counter


}

};
