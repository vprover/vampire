/**
 * @file EqualityFactoring.cpp
 * Implements class EqualityFactoring.
 */

#include <utility>

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Unit.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "EqualityFactoring.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct EqualityFactoring::IsPositiveEqualityFn
{
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { return l->isEquality() && l->isPositive(); }
};
struct EqualityFactoring::IsDifferentPositiveEqualityFn
{
  IsDifferentPositiveEqualityFn(Literal* lit) : _lit(lit) {}
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l2)
  { return l2->isEquality() && l2->polarity() && l2!=_lit; }
private:
  Literal* _lit;
};

struct EqualityFactoring::FactorablePairsFn
{
  FactorablePairsFn(Clause* cl) : _cl(cl) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*,TermList>,pair<Literal*,TermList> > >);
  OWN_RETURN_TYPE operator() (pair<Literal*,TermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg,
	    getMapAndFlattenIterator(
		    getFilteredIterator(
			    getContentIterator(*_cl),
			    IsDifferentPositiveEqualityFn(arg.first)),
		    EqHelper::EqualityArgumentIteratorFn())) );
  }
private:
  Clause* _cl;
};

struct EqualityFactoring::ResultFn
{
  ResultFn(Clause* cl, EqualityFactoring& parent)
      : _cl(cl), _cLen(cl->length()), _ordering(parent._salg->getOrdering()) {}
  DECL_RETURN_TYPE(Clause*);
  Clause* operator() (pair<pair<Literal*,TermList>,pair<Literal*,TermList> > arg)
  {
    CALL("EqualityFactoring::ResultFn::operator()");

    Literal* sLit=arg.first.first; //selected literal
    Literal* fLit=arg.second.first; //factored-out literal
    ASS(sLit->isEquality());
    ASS(fLit->isEquality());

    unsigned srt = SortHelper::getEqualityArgumentSort(sLit);
    if(srt!=SortHelper::getEqualityArgumentSort(fLit)) {
      return false;
    }

    TermList sLHS=arg.first.second;
    TermList sRHS=EqHelper::getOtherEqualitySide(sLit, sLHS);
    TermList fLHS=arg.second.second;
    TermList fRHS=EqHelper::getOtherEqualitySide(fLit, fLHS);
    ASS_NEQ(sLit, fLit);

    static RobSubstitution subst;
    subst.reset();
    if(!subst.unify(sLHS,0,fLHS,0)) {
      return 0;
    }

    TermList sLHSS=subst.apply(sLHS,0);
    TermList sRHSS=subst.apply(sRHS,0);
    if(_ordering.compare(sRHSS,sLHSS)==Ordering::GREATER) {
      return 0;
    }
    TermList fRHSS=subst.apply(fRHS,0);
    if(_ordering.compare(fRHSS,sRHSS)==Ordering::GREATER) {
      return 0;
    }

    Inference* inf = new Inference1(Inference::EQUALITY_FACTORING, _cl);
    Clause* res = new(_cLen) Clause(_cLen, _cl->inputType(), inf);

    (*res)[0]=Literal::createEquality(false, sRHSS, fRHSS, srt);

    unsigned next = 1;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=fLit) {
	(*res)[next++] = subst.apply(curr, 0);
      }
    }
    ASS_EQ(next,_cLen);

    res->setAge(_cl->age()+1);
    env.statistics->equalityFactoring++;

    return res;
  }
private:
  Clause* _cl;
  unsigned _cLen;
  Ordering& _ordering;
};

ClauseIterator EqualityFactoring::generateClauses(Clause* premise)
{
  CALL("EqualityFactoring::generateClauses");

  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->selected()>0);

  return pvi( getFilteredIterator(
	  getMappingIterator(
		  getMapAndFlattenIterator(
			  getMapAndFlattenIterator(
				  getFilteredIterator(
					  premise->getSelectedLiteralIterator(),
					  IsPositiveEqualityFn()),
				  EqHelper::LHSIteratorFn(_salg->getOrdering())),
			  FactorablePairsFn(premise)),
		  ResultFn(premise, *this)),
	  NonzeroFn()) );

}

}
