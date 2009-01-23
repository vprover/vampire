/**
 * @file Factoring.cpp
 * Implements class Factoring.
 */

#include <utility>

#include "../Lib/Int.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
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

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * This functor, given pair of unsigned integers,
 * returns iterator of pairs of unification of literals at
 * positions corresponding to these integers and one
 * of these literals. (Literal stays the same and unifiers vary.)
 */
class FactoringUnificationsFn
{
public:
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*,MMSubstitution*> >);
  FactoringUnificationsFn(Clause* cl)
  : _cl(cl)
  {
    _subst=MMSubstitutionSP(new MMSubstitution());
  }
  OWN_RETURN_TYPE operator() (pair<unsigned,unsigned> nums)
  {
    CALL("FactoringUnificationsFn::operator()");

    //we assume there are no duplicate literals
    ASS((*_cl)[nums.first]!=(*_cl)[nums.second]);
    ASS_EQ(_subst->size(),0);

    SubstIterator unifs=_subst->unifiers((*_cl)[nums.first],0,(*_cl)[nums.second],0, false);
    if(!unifs.hasNext()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pushPairIntoRightIterator((*_cl)[nums.second], unifs);
  }
private:
  Clause* _cl;
  MMSubstitutionSP _subst;
};

/**
 * This functor given a pair of a literal and a substitution,
 * removes the literal from the clause specified in constructor,
 * applies the substitution, and returns resulting clause.
 * (Also it records this to statistics as factoring.)
 */
class FactoringResultsFn
{
public:
  DECL_RETURN_TYPE(Clause*);
  FactoringResultsFn(Clause* cl)
  : _cl(cl), _cLen(cl->length()) {}
  OWN_RETURN_TYPE operator() (pair<Literal*,MMSubstitution*> arg)
  {
    CALL("FactoringResultsFn::operator()");

    unsigned newLength = _cLen-1;
    Inference* inf = new Inference1(Inference::FACTORING, _cl);
    Clause* res = new(newLength) Clause(newLength, _cl->inputType(), inf);

    unsigned next = 0;
    Literal* skipped=arg.first;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=skipped) {
	(*res)[next++] = arg.second->apply(curr, 0);
      }
    }
    ASS_EQ(next,newLength);

    res->setAge(_cl->age()+1);
    env.statistics->factoring++;

    return res;
  }
private:
  Clause* _cl;
  ///length of the premise clause
  unsigned _cLen;
};

ClauseIterator Factoring::generateClauses(Clause* premise)
{
  CALL("Factoring::generateClauses");

  ASS(premise->selected()>0);
  if(premise->selected()==1) {
    return ClauseIterator::getEmpty();
  }
  return getMappingIterator(
	  getFlattenedIterator(
		  getMappingIterator(getCombinationIterator(0u,premise->selected()),
			  FactoringUnificationsFn(premise))),
	  FactoringResultsFn(premise));
}

}
