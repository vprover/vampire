/**
 * @file EqualityResolution.cpp
 * Implements class EqualityResolution.
 */

#include <utility>

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/PairUtils.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/RobSubstitution.hpp"
#include "../Kernel/EqHelper.hpp"
#include "../Kernel/Ordering.hpp"

#include "EqualityResolution.hpp"

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

struct EqualityResolution::IsNegativeEqualityFn
{
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl), _cLen(cl->length()) {}
  DECL_RETURN_TYPE(Clause*);
  Clause* operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    static RobSubstitution subst;
    subst.reset();
    if(!subst.unify(*lit->nthArgument(0),0,*lit->nthArgument(1),0)) {
      return 0;
    }
    unsigned newLen=_cLen-1;

    Inference* inf = new Inference1(Inference::EQUALITY_RESOLUTION, _cl);
    Clause* res = new(newLen) Clause(newLen, _cl->inputType(), inf);

    unsigned next = 0;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
	(*res)[next++] = subst.apply(curr, 0);
      }
    }
    ASS_EQ(next,newLen);

    res->setAge(_cl->age()+1);
    env.statistics->equalityResolution++;

    return res;
  }
private:
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  CALL("EqualityResolution::generateClauses");

  ASS(premise->selected()>0);
  if(premise->length()==1) {
    return ClauseIterator::getEmpty();
  }

  return pvi( getFilteredIterator(
	  getMappingIterator(
		  getFilteredIterator(
			  premise->getSelectedLiteralIterator(),
			  IsNegativeEqualityFn()),
		  ResultFn(premise)),
	  NonzeroFn()) );

}

}
