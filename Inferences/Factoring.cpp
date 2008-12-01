/**
 * @file Factoring.cpp
 * Implements class Factoring.
 */


#include "../Lib/Int.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/MMSubstitution.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "Factoring.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;


/**
 * Iterator over all factors of a clause yielded by unification of
 * two of its literals.
 */
class FactoringResultIterator
: public IteratorCore<Clause*>
{
public:
  FactoringResultIterator(Clause* cl)
  : _cl(cl), _selCnt(_cl->selected()),
  _lit1(0), _lit2(0), _nextUnificationReady(false), _lits(_cl->selected())
  {
    ASS(_selCnt>1);
    _lits.initFromArray(_selCnt, *_cl);
    _lits.sort<LiteralHeaderComparator>(_selCnt);
  }
  bool hasNext()
  {
    return _nextUnificationReady || getNextUnificationReady();
  }
  Clause* next()
  {
    CALL("FactoringResultIterator::next");

    ASS(_nextUnificationReady);
    _nextUnificationReady=false;

    unsigned clength = _cl->length();
    unsigned newLength = clength-1;

    Inference* inf = new Inference1(Inference::FACTORING, _cl);

    Clause* res = new(newLength) Clause(newLength, _cl->inputType(), inf);

    unsigned next = 0;
    Literal* skipped=_lits[_lit2];
    for(unsigned i=0;i<clength;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=skipped) {
	(*res)[next++] = _subst.apply(curr, 0);
      }
    }
    ASS_EQ(next,newLength);

    res->setAge(_cl->age()+1);
    env.statistics->factoring++;

    return res;
  }
private:
  struct LiteralHeaderComparator
  {
    static Comparison compare(Literal* l1, Literal* l2)
    { return Int::compare(l1->header(), l2->header()); }
  };

  bool getNextUnificationReady()
  {
    CALL("FactoringResultIterator::getNextUnificationReady");
    ASS(_selCnt>1);
    ASS(!_nextUnificationReady);

    _subst.reset();

    for(;;) {
      _lit2++;
      ASS(_lit2<=_selCnt);
      if(_lit2==_selCnt) {
	_lit1++;
	_lit2=_lit1+1;
	if(_lit2>=_selCnt) {
	  return false;
	}
      }
      if( _lits[_lit1]->header()==_lits[_lit2]->header() ) {
	if( _subst.unify(_lits[_lit1],0, _lits[_lit2],0) ) {
	  _nextUnificationReady=true;
	  return true;
	}
      } else {
	_lit2 = ++_lit1;
      }
    }
  }
  Clause* _cl;
  MMSubstitution _subst;
  unsigned _selCnt;
  unsigned _lit1;
  unsigned _lit2;
  bool _nextUnificationReady;
  DArray<Literal*> _lits;
};

ClauseIterator Factoring::generateClauses(Clause* premise)
{
  CALL("Factoring::generateClauses");
  ASS(premise->selected()>0);
  if(premise->selected()==1) {
    return ClauseIterator::getEmpty();
  }

  return ClauseIterator(new FactoringResultIterator(premise));
}
