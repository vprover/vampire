/**
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/PairUtils.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Shell/Statistics.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "BinaryResolution.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BinaryResolution::attach(SaturationAlgorithm* salg)
{
  CALL("BinaryResolution::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<GeneratingLiteralIndex*> (
	  _salg->getIndexManager()->request(GENERATING_SUBST_TREE) );
}

void BinaryResolution::detach()
{
  CALL("BinaryResolution::detach");

  _index=0;
  _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}


struct ResolutionUnificationsFn
{
  ResolutionUnificationsFn(GeneratingLiteralIndex* index)
  : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, SLQueryResult> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
  }
private:
  GeneratingLiteralIndex* _index;
};

struct ResolutionResultFn
{
  ResolutionResultFn(Clause* cl)
  : _cl(cl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, SLQueryResult> arg)
  {
    SLQueryResult& qr = arg.second;
    Literal* resLit = arg.first;

    int clength = _cl->length();
    int dlength = qr.clause->length();
    int newLength = clength+dlength-2;

    Inference* inf = new Inference2(Inference::RESOLUTION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType)
    	Int::max(_cl->inputType(), qr.clause->inputType());

    Clause* res = new(newLength) Clause(newLength, inpType, inf);

    int next = 0;
    for(int i=0;i<clength;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=resLit) {
	//query term variables are in variable bank 0
	(*res)[next++] = qr.substitution->apply(curr, 0);
      }
    }
    for(int i=0;i<dlength;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
	//query term variables are in variable bank 1
	(*res)[next++] = qr.substitution->apply(curr, 1);
      }
    }

    res->setAge(Int::max(_cl->age(),qr.clause->age())+1);
    env.statistics->resolution++;

    return res;
  }
private:
  Clause* _cl;
};


ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  return pvi( getMappingIterator(
	  getFlattenedIterator(
		  getMappingIterator(
			  getContentIterator(*premise),
			  ResolutionUnificationsFn(_index))),
	  ResolutionResultFn(premise)) );
}

}
