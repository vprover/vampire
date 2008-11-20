/**
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution.
 */

#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "BinaryResolution.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inference;

void BinaryResolution::attach(SaturationAlgorithm* salg)
{
  _index=_salg->getIndexManager()->request(GENERATING_SUBST_TREE);
}

BinaryResolution::~BinaryResolution()
{
  _index=0;
  _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
}

class BinaryResolutionResultIterator
: IteratorCore<Clause*>
{
public:
  BinaryResolutionResultIterator(Index* index, Clause* cl)
  : _index(index), _cl(cl), _nextLit(0),
  _uit(SLQueryResultIterator::getEmpty())
  {
    
  }
  bool hasNext()
  {
    if(_uit.hasNext()) {
      return true;
    }
    return _nextLit < _cl->selected();
  }
  Clause* next()
  {
    SLQueryResult qr = getNextUnification();
    
    int clength = _cl->length();
    int dlength = qr.clause->length();
    int newLength = clength+dlength-2;
    
    Inference* inf = new Inference2(Inference::RESOLUTION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType) 
    	Int::max(_cl->inputType(),
	    qr.clause->inputType())
    
    Clause* res = new(newLength)
    	Clause(newLength,
	    ,
		    inf);
    int next = 0;
    for (int f = newLength-1;f >= 0;f--) {
      if (lits[f]) {
	(*res)[next++] = lits[f];
      }
    }
    res->setAge(Int::max(_clause.age(),d->age())+1);
    _pa.unprocessed().insert(res);
    
    
  }
private:
  SLQueryResult getNextUnification()
  {
    while(!_uit.hasNext()) {
      _lit=(*_cl)[_nextLit++];
      _uit=_index->getComplementaryUnifications(_lit);
    }
    return _uit.next();
  }
  Index* _index;
  Clause* _cl;
  Literal* _lit;
  int _nextLit;
  SLQueryResultIterator _uit;
};

ClauseIterator BinaryResolution::generateClauses(Clause* cl1)
{
  CALL("BinaryResolution::generateClauses");

  int selCnt=cl1->selected();
  ASS(selCnt>0);
  for(int li=0;li<selCnt;li++) {
    Literal* lit1=(*cl1)[li];
    SLQueryResultIterator unifs=_index->getComplementaryUnifications(lit1);
  }
}
