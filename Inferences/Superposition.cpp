/**
 * @file Superposition.cpp
 * Implements class Superposition.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/PairUtils.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Shell/Statistics.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Ordering.hpp"
#include "../Kernel/EqHelper.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Indexing/TermSharing.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "Superposition.hpp"

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

void Superposition::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SuperpositionSubtermIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<SuperpositionLHSIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_LHS_SUBST_TREE) );
}

void Superposition::detach()
{
  CALL("Superposition::detach");

  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(SUPERPOSITION_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}



struct Superposition::RewritableResultsFn
{
  RewritableResultsFn(SuperpositionSubtermIndex* index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
  }
private:
  SuperpositionSubtermIndex* _index;
};

struct Superposition::RewriteableSubtermsFn
{
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, EqHelper::getRewritableSubtermIterator(lit)) );
  }
};

struct Superposition::ApplicableRewritesFn
{
  ApplicableRewritesFn(SuperpositionLHSIndex* index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
  }
private:
  SuperpositionLHSIndex* _index;
};


struct Superposition::ForwardResultFn
{
  ForwardResultFn(Clause* cl, Limits* limits) : _cl(cl), _limits(limits) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return performSuperposition(_cl, arg.first.first, arg.first.second,
	    qr.clause, qr.literal, qr.term, qr.substitution, true, _limits);
  }
private:
  Clause* _cl;
  Limits* _limits;
};


struct Superposition::BackwardResultFn
{
  BackwardResultFn(Clause* cl, Limits* limits) : _cl(cl), _limits(limits) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return performSuperposition(qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, _limits);
  }
private:
  Clause* _cl;
  Limits* _limits;
};


ClauseIterator Superposition::generateClauses(Clause* premise)
{
  CALL("Superposition::generateClauses");
  Limits* limits=_salg->getLimits();

  return pvi( getFilteredIterator(
	getConcatenatedIterator(
	  getMappingIterator(
		  getMapAndFlattenIterator(
			  getMapAndFlattenIterator(
				  premise->getSelectedLiteralIterator(),
				  RewriteableSubtermsFn()),
			  ApplicableRewritesFn(_lhsIndex)),
		  ForwardResultFn(premise, limits)),
	  getMappingIterator(
		  getMapAndFlattenIterator(
			  getMapAndFlattenIterator(
				  premise->getSelectedLiteralIterator(),
				  EqHelper::LHSIteratorFn()),
			  RewritableResultsFn(_subtermIndex)),
		  BackwardResultFn(premise, limits))),
	NonzeroFn()) );
}

/**
 * If superposition should be performed, return result of the superposition,
 * otherwise return 0.
 */
Clause* Superposition::performSuperposition(
	Clause* rwClause, Literal* rwLit, TermList rwTerm,
	Clause* eqClause, Literal* eqLit, TermList eqLHS,
	ResultSubstitutionSP subst, bool eqIsResult, Limits* limits)
{
  CALL("Superposition::performSuperposition");

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  int newAge=Int::max(rwClause->age(),eqClause->age())+1;

  bool shouldCheckWeight=false;
  int weightLimit;
  if(limits->ageLimited() && newAge > limits->ageLimit() && limits->weightLimited()) {
    weightLimit=limits->weightLimit();
    shouldCheckWeight=true;

    int wlb=0;//weight lower bound
    for(unsigned i=0;i<rwLength;i++) {
      Literal* curr=(*rwClause)[i];
      if(curr!=rwLit) {
  	wlb+=curr->weight();
      }
    }
    for(unsigned i=0;i<eqLength;i++) {
      Literal* curr=(*eqClause)[i];
      if(curr!=eqLit) {
  	wlb+=curr->weight();
      }
    }
    if(wlb > weightLimit) {
      return 0;
    }
  }

  static Ordering* ordering=0;
  if(!ordering) {
    ordering=Ordering::instance();
  }

  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);
  TermList eqLHSS = subst->apply(eqLHS, eqIsResult);
  TermList tgtTerm = EqHelper::getRHS(eqLit, eqLHS);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);

  //check that we're not rewriting smaller subterm with larger
  if(ordering->compare(tgtTermS,eqLHSS)==Ordering::GREATER) {
    return 0;
  }
  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,tgtTermS);
  if(tgtLitS->isEquality()) {
    //check that we're not rewriting only the smaller side of an equality
    TermList arg0=*tgtLitS->nthArgument(0);
    TermList arg1=*tgtLitS->nthArgument(1);
    if(!arg0.containsSubterm(tgtTermS)) {
      if(ordering->compare(arg0,arg1)==Ordering::GREATER) {
	return 0;
      }
    } else if(!arg1.containsSubterm(tgtTermS)) {
      if(ordering->compare(arg1,arg0)==Ordering::GREATER) {
	return 0;
      }
    }
  }

  unsigned newLength = rwLength+eqLength-1;

  Inference* inf = new Inference2(Inference::SUPERPOSITION, rwClause, eqClause);
  Unit::InputType inpType = (Unit::InputType)
  	Int::max(rwClause->inputType(), eqClause->inputType());

  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  int weight=0;
  (*res)[0] = tgtLitS;
  int next = 1;
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit) {
      (*res)[next++] = subst->apply(curr, !eqIsResult);
      if(shouldCheckWeight) {
	weight+=(*res)[next++]->weight();
	if(weight>weightLimit) {
	  goto weight_fail;
	}
      }
    }
  }
  for(unsigned i=0;i<eqLength;i++) {
    Literal* curr=(*eqClause)[i];
    if(curr!=eqLit) {
      (*res)[next++] = subst->apply(curr, eqIsResult);
      if(shouldCheckWeight) {
	weight+=(*res)[next++]->weight();
	if(weight>weightLimit) {
	  goto weight_fail;
	}
      }
    }
  }

weight_fail:
  if(shouldCheckWeight && weight>weightLimit) {
    res->destroy();
    return 0;
  }

  res->setAge(newAge);
  if(eqIsResult) {
    env.statistics->forwardSuperposition++;
  } else {
    env.statistics->backwardSuperposition++;
  }

  return res;
}

}
