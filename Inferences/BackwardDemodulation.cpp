/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file BackwardDemodulation.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BackwardDemodulation.hpp"

namespace Inferences {

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardDemodulation::attach(SaturationAlgorithm* salg)
{
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
  _helper = DemodulationHelper(getOptions(), &_salg->getOrdering());
}

void BackwardDemodulation::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

struct BackwardDemodulation::RemovedIsNonzeroFn
{
  bool operator() (BwSimplificationRecord arg)
  {
    return arg.toRemove!=0;
  }
};

struct BackwardDemodulation::RewritableClausesFn
{
  RewritableClausesFn(DemodulationSubtermIndex* index) : _index(index) {}
  VirtualIterator<pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> > operator() (TypedTermList lhs)
  {
    return pvi( pushPairIntoRightIterator(lhs, _index->getInstances(lhs, true)) );
  }
private:
  DemodulationSubtermIndex* _index;
};

namespace {

struct Applicator : SubstApplicator {
  Applicator(ResultSubstitution* subst) : subst(subst) {}
  TermList operator()(unsigned v) const override {
    return subst->applyToBoundQuery(TermList(v,false));
  }
  ResultSubstitution* subst;
};

} // end namespace

struct BackwardDemodulation::ResultFn
{
  typedef DHMultiset<Clause*> ClauseSet;

  ResultFn(Clause* cl, BackwardDemodulation& parent, const DemodulationHelper& helper)
  : _cl(cl), _helper(helper), _ordering(parent._salg->getOrdering())
  {
    ASS_EQ(_cl->length(),1);
    _eqLit=(*_cl)[0];
    _removed=SmartPtr<ClauseSet>(new ClauseSet());
  }

  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  BwSimplificationRecord operator() (pair<TermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg)
  {
    auto qr=arg.second;

    if( !ColorHelper::compatible(_cl->color(), qr.data->clause->color()) ) {
      //colors of premises don't match
      return BwSimplificationRecord(0);
    }

    if(_cl==qr.data->clause || _removed->find(qr.data->clause)) {
      //the retrieved clause was already replaced during this
      //backward demodulation
      return BwSimplificationRecord(0);
    }

    TermList lhs=arg.first;
    TermList rhs=EqHelper::getOtherEqualitySide(_eqLit, lhs);

    // AYB there used to be a check here to ensure that the sorts
    // matched. This is no longer necessary, as sort matching / unification
    // is handled directly within the tree

    auto subs = qr.unifier;
    ASS(subs->isIdentityOnResultWhenQueryBound());

    Applicator appl(subs.ptr());

    TermList lhsS=qr.data->term;

    if (_ordering.compareUnidirectional(AppliedTerm(lhsS), AppliedTerm(rhs,&appl,true))!=Ordering::GREATER) {
      return BwSimplificationRecord(0);
    }

    TermList rhsS=subs->applyToBoundQuery(rhs);

    if (_helper.redundancyCheckNeededForPremise(qr.data->clause,qr.data->literal,lhsS) &&
      !_helper.isPremiseRedundant(qr.data->clause,qr.data->literal,lhsS,rhsS,lhs,&appl))
    {
      return BwSimplificationRecord(0);
    }

    Literal* resLit=EqHelper::replace(qr.data->literal,lhsS,rhsS);
    if(EqHelper::isEqTautology(resLit)) {
      env.statistics->backwardDemodulationsToEqTaut++;
      _removed->insert(qr.data->clause);
      return BwSimplificationRecord(qr.data->clause);
    }

    unsigned cLen=qr.data->clause->length();
    RStack<Literal*> resLits;

    resLits->push(resLit);

    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*qr.data->clause)[i];
      if(curr!=qr.data->literal) {
        resLits->push(curr);
      }
    }

    _removed->insert(qr.data->clause);
    Clause *replacement = Clause::fromStack(
      *resLits,
      SimplifyingInference2(InferenceRule::BACKWARD_DEMODULATION, qr.data->clause, _cl)
    );
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(replacement, new BackwardDemodulationExtra(lhs, lhsS));
    return BwSimplificationRecord(qr.data->clause, replacement);
  }
private:
  Literal* _eqLit;
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;

  const DemodulationHelper& _helper;

  Ordering& _ordering;
};


void BackwardDemodulation::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  TIME_TRACE("backward demodulation");

  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    simplifications=BwSimplificationRecordIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];

  BwSimplificationRecordIterator replacementIterator=
    pvi( getFilteredIterator(
	    getMappingIterator(
		    getMapAndFlattenIterator(
			    EqHelper::getDemodulationLHSIterator(lit,
            _salg->getOptions().backwardDemodulation() == Options::Demodulation::PREORDERED,
            _salg->getOrdering()).first,
			    RewritableClausesFn(_index)),
		    ResultFn(cl, *this, _helper)),
 	    RemovedIsNonzeroFn()) );

  //here we know that the getPersistentIterator evaluates all items of the
  //replacementIterator right at this point, so we can measure the time just
  //simply (which cannot be generally done when iterators are involved)

  simplifications=getPersistentIterator(replacementIterator);
}

}
