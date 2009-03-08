/**
 * @file BestLiteralSelector.hpp
 * Defines classes BestLiteralSelector and CompleteBestLiteralSelector.
 */


#ifndef __BestLiteralSelector__
#define __BestLiteralSelector__

#include <algorithm>

#include "../Forwards.hpp"

#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/Stack.hpp"

#include "Term.hpp"
#include "Clause.hpp"
#include "Ordering.hpp"

#include "LiteralSelector.hpp"

namespace Kernel {

using namespace Lib;

/**
 * A literal selector class template, that select the best literal
 * (i.e. the maximal literal in quality ordering specfied by
 * QComparator class). Using this literal selector does not
 * sustain completeness.
 *
 * Objects of the QComparator class must provide a method
 * Lib::Comparison compare(Literal*, Literal*)
 * that compares the quality of two literals.
 */
template<class QComparator>
class BestLiteralSelector
: public LiteralSelector
{
public:
  BestLiteralSelector() {}
  void select(Clause* c)
  {
    CALL("BestLiteralSelector::select");

    unsigned clen=c->length();

    if(clen<=1) {
      c->setSelected(clen);
      return;
    }

    unsigned besti=0;
    Literal* best=(*c)[0];
    for(unsigned i=1;i<clen;i++) {
      if(_comp.compare(best, (*c)[i])==LESS) {
        besti=i;
        best=(*c)[i];
      }
    }
    if(besti>0) {
      std::swap((*c)[0], (*c)[besti]);
    }
    c->setSelected(1);
  }

private:
  QComparator _comp;
};


/**
 * A literal selector class template, that tries select the best
 * literal (i.e. the maximal literal in quality ordering specfied by
 * QComparator class), but takes completness of the selection into
 * account.
 *
 * If the best literal is negative, it is selected. If it is among
 * maximal literals, and there is no negative literal among them,
 * they all are selected. If there is a negative literal among
 * maximal literals, we select the best negative literal. If
 * the best literal is neither negative nor maximal, we consider
 * similarly the second best etc...
 *
 * Objects of the QComparator class must provide a method
 * Lib::Comparison compare(Literal*, Literal*)
 * that compares the quality of two literals.
 */
template<class QComparator>
class CompleteBestLiteralSelector
: public LiteralSelector
{
public:
  CompleteBestLiteralSelector() : _ord(Ordering::instance()) {}
  void select(Clause* c)
  {
    CALL("CompleteBestLiteralSelector::select");

    unsigned clen=c->length();

    if(clen<=1) {
      c->setSelected(clen);
      return;
    }

    static DArray<Literal*> litArr(64);
    litArr.initFromArray(clen,*c);
    litArr.sortInversed(_comp);

    LiteralList* maximals=0;
    Literal* singleSelected=0; //If equals to 0 in the end, all maximal
			       //literals will be selected.

    if(litArr[0]->isNegative()) {
      singleSelected=litArr[0];
    } else {
      DArray<Literal*>::ReversedIterator rlit(litArr);
      while(rlit.hasNext()) {
	LiteralList::push(rlit.next(),maximals);
      }
      _ord->removeNonMaximal(maximals);
      unsigned besti=0;
      while(true) {
	if(maximals->head()==litArr[besti]) {
	  break;
	}
	besti++;
	ASS_L(besti,clen);
	if(litArr[besti]->isNegative()) {
	  singleSelected=litArr[besti];
	  break;
	}
      }
    }
    if(!singleSelected && !maximals->tail()) {
	//there is only one maximal literal
	singleSelected=maximals->head();
    }
    if(!singleSelected) {
      for(LiteralList* mit=maximals; mit; mit=mit->tail()) {
	if(mit->head()->isNegative()) {
	  for(unsigned i=1;i<clen;i++) {
	    if(litArr[i]->isNegative()) {
	      singleSelected=litArr[i];
	    }
	  }
	  ASS(singleSelected);
	  break;
	}
      }
    }
    if(!singleSelected) {
      //select multiple maximal literals
      static Stack<Literal*> replaced(16);
      Set<Literal*> maxSet;
      unsigned selCnt=0;

      for(LiteralList* mit=maximals; mit; mit=mit->tail()) {
	maxSet.insert(mit->head());
      }

      while(maximals) {
	if(!maxSet.contains((*c)[selCnt])) {
	  replaced.push((*c)[selCnt]);
	}
	(*c)[selCnt]=LiteralList::pop(maximals);
	selCnt++;
      }
      ASS_G(selCnt,1);

      //put back non-selected literals, that were removed
      unsigned i=selCnt;
      while(replaced.isNonEmpty()) {
	while(!maxSet.contains((*c)[i])) {
	  i++;
	  ASS_L(i,clen);
	}
	(*c)[selCnt]=replaced.pop();
      }

      c->setSelected(selCnt);
    } else {
      unsigned besti=0;
      while((*c)[besti]!=singleSelected) {
	besti++;
	ASS_L(besti,clen);
      }
      if(besti!=0) {
	std::swap((*c)[0],(*c)[besti]);
      }
      c->setSelected(1);
    }
    maximals->destroy();
  }

private:
  QComparator _comp;
  Ordering* _ord;
};

};

#endif /* __BestLiteralSelector__ */
