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


struct BinaryResolution::UnificationsFn
{
  UnificationsFn(GeneratingLiteralIndex* index)
  : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, SLQueryResult> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
  }
private:
  GeneratingLiteralIndex* _index;
};

struct BinaryResolution::ResultFn
{
  ResultFn(Clause* cl, Limits* limits)
  : _cl(cl), _limits(limits) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, SLQueryResult> arg)
  {
    CALL("BinaryResolution::ResultFn::operator()");

    SLQueryResult& qr = arg.second;
    Literal* resLit = arg.first;

    unsigned clength = _cl->length();
    unsigned dlength = qr.clause->length();
    int newAge=Int::max(_cl->age(),qr.clause->age())+1;
    bool shouldLimitWeight=_limits->ageLimited() && newAge > _limits->ageLimit()
	&& _limits->weightLimited();

    if(shouldLimitWeight) {
      int wlb=0;//weight lower bound
      for(unsigned i=0;i<clength;i++) {
        Literal* curr=(*_cl)[i];
        if(curr!=resLit) {
          wlb+=curr->weight();
        }
      }
      for(unsigned i=0;i<dlength;i++) {
        Literal* curr=(*qr.clause)[i];
        if(curr!=qr.literal) {
          wlb+=curr->weight();
        }
      }
      if(wlb > _limits->weightLimit()) {
        return 0;
      }
    }

    unsigned newLength = clength+dlength-2;

    Inference* inf = new Inference2(Inference::RESOLUTION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType)
    	Int::max(_cl->inputType(), qr.clause->inputType());

    Clause* res = new(newLength) Clause(newLength, inpType, inf);

    unsigned next = 0;
    for(unsigned i=0;i<clength;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=resLit) {
	(*res)[next++] = qr.substitution->applyToQuery(curr);
      }
    }
    for(unsigned i=0;i<dlength;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
	(*res)[next++] = qr.substitution->applyToResult(curr);
      }
    }

    res->setAge(newAge);
    env.statistics->resolution++;

    return res;
  }
private:
  Clause* _cl;
  Limits* _limits;
};


ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  Limits* limits=_salg->getLimits();
  return pvi( getFilteredIterator(
      getMappingIterator(
	  getFlattenedIterator(
		  getMappingIterator(
			  premise->getSelectedLiteralIterator(),
			  UnificationsFn(_index))),
	  ResultFn(premise, limits)),
      NonzeroFn()) );
}

}
