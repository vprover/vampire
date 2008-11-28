/**
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution.
 */

#include "../Lib/Int.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "BinaryResolution.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void BinaryResolution::attach(SaturationAlgorithm* salg)
{
  CALL("BinaryResolution::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=_salg->getIndexManager()->request(GENERATING_SUBST_TREE);
}

void BinaryResolution::detach()
{
  CALL("BinaryResolution::detach");

  _index=0;
  _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

class BinaryResolutionResultIterator
: public IteratorCore<Clause*>
{
public:
  BinaryResolutionResultIterator(Index* index, Clause* cl)
  : _index(index), _cl(cl), _nextLit(0),
  _uit(SLQueryResultIterator::getEmpty()), _nextUnificationReady(false)
  {

  }
  bool hasNext()
  {
    return _nextUnificationReady || getNextUnificationReady();
  }
  Clause* next()
  {
    CALL("BinaryResolutionResultIterator::next");

    ASS(_nextUnificationReady);
    SLQueryResult& qr = _nextUnification;
    _nextUnificationReady=false;

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
      if(curr!=_lit) {
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

    return res;
  }
private:
  bool getNextUnificationReady()
  {
    ASS(!_nextUnificationReady);
    while(!_uit.hasNext()) {
      if(_nextLit == _cl->selected()) {
	return false;
      }
      _lit=(*_cl)[_nextLit++];
      _uit=_index->getComplementaryUnifications(_lit);
    }
    _nextUnification=_uit.next();
    _nextUnificationReady=true;
    return true;
  }
  Index* _index;
  Clause* _cl;
  Literal* _lit;
  /** Index of the next literal, we'll be trying to unify,
   * after we consume all results in @b _uit */
  unsigned _nextLit;
  SLQueryResultIterator _uit;
  SLQueryResult _nextUnification;
  bool _nextUnificationReady;
};

ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  return ClauseIterator(new BinaryResolutionResultIterator(_index, premise));
}
