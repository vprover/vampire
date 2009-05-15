/**
 * @file Factoring.cpp
 * Implements class Factoring.
 */

#include <utility>

#include "../Lib/Int.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/PairUtils.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/RobSubstitution.hpp"

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
class Factoring::UnificationsFn
{
public:
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*,RobSubstitution*> >);
  UnificationsFn(Clause* cl)
  : _cl(cl)
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  OWN_RETURN_TYPE operator() (pair<unsigned,unsigned> nums)
  {
    CALL("Factoring::UnificationsFn::operator()");

    //we assume there are no duplicate literals
    ASS((*_cl)[nums.first]!=(*_cl)[nums.second]);
    ASS_EQ(_subst->size(),0);

    SubstIterator unifs=_subst->unifiers((*_cl)[nums.first],0,(*_cl)[nums.second],0, false);
    if(!unifs.hasNext()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pvi( pushPairIntoRightIterator((*_cl)[nums.second], unifs) );
  }
private:
  Clause* _cl;
  RobSubstitutionSP _subst;
};

/**
 * This functor given a pair of a literal and a substitution,
 * removes the literal from the clause specified in constructor,
 * applies the substitution, and returns resulting clause.
 * (Also it records this to statistics as factoring.)
 */
class Factoring::ResultsFn
{
public:
  DECL_RETURN_TYPE(Clause*);
  ResultsFn(Clause* cl)
  : _cl(cl), _cLen(cl->length()) {}
  OWN_RETURN_TYPE operator() (pair<Literal*,RobSubstitution*> arg)
  {
    CALL("Factoring::ResultsFn::operator()");

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

/**
 * Return ClauseIterator, that yields clauses generated from
 * @b premise by the factoring inference rule.
 *
 * Nothing is generated, when the premise contains only one
 * negative literal. Otherwise one of literals used in factoring
 * has to be selected, the other one does not. This deviation from
 * usual factoring rules, where both factored literals have to be
 * selected, is for the sake of incmoplete literal selection
 * functions, that select always just one literal. (This would lead
 * to no factoring at all.)
 *
 * If a complete literal selection is used, this makes no difference,
 * as when two literals are unifiable, one cannot be maximal and the
 * other non-maximal in the literal ordering.
 */
ClauseIterator Factoring::generateClauses(Clause* premise)
{
  CALL("Factoring::generateClauses");

  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  if(premise->selected()==1 && (*premise)[0]->isNegative()) {
    return ClauseIterator::getEmpty();
  }
  return pvi( getMappingIterator(
	  getMapAndFlattenIterator(
		  getCombinationIterator(0u,premise->selected(),premise->length()),
		  UnificationsFn(premise)),
	  ResultsFn(premise)) );
}

}
