/**
 * @file ForwardDemodulation.cpp
 * Implements class ForwardDemodulation.
 */

#include "../Lib/Int.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/TimeCounter.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/EqHelper.hpp"
#include "../Kernel/Ordering.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Renaming.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/TermIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
#include "../Shell/Statistics.hpp"

#include "ForwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE) );
}

void ForwardDemodulation::detach()
{
  CALL("ForwardDemodulation::detach");
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


void ForwardDemodulation::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("ForwardDemodulation::perform");

  TimeCounter tc(TC_FORWARD_DEMODULATION);

  static Ordering* ordering=Ordering::instance();

  //Perhaps it might be a good idea to try to
  //replace subterms in some special order, like
  //the heaviest first...

  //TODO: Add completeness check:
  //
  //h(a,a,a)=f(a,a)       g(h(a,a,a))=a (DEL)
  //-----------------------------------------
  //               g(f(a,a))=a
  //
  //is incomplete as the premise is greated than the demodulated clause

  unsigned cLen=cl->length();
  for(unsigned li=0;li<cLen;li++) {
    Literal* lit=(*cl)[li];
    Term::NonVariableIterator nvi(lit);
    while(nvi.hasNext()) {
      TermList trm=nvi.next();
      TermQueryResultIterator git=_index->getGeneralizations(trm, true);
      while(git.hasNext()) {
	TermQueryResult qr=git.next();
	ASS_EQ(qr.clause->length(),1);

	TermList rhs=EqHelper::getRHS(qr.literal,qr.term);


	TermList rhsS;
	if(!qr.substitution->isIdentityOnQueryWhenResultBound()) {
	  //When we apply substitution to the rhs, we get a term, that is
	  //a variant of the term we'd like to get, as new variables are
	  //produced in the substitution application.
	  TermList lhsSBadVars=qr.substitution->applyToResult(qr.term);
	  TermList rhsSBadVars=qr.substitution->applyToResult(rhs);
	  Renaming rNorm, qNorm, qDenorm;
	  rNorm.normalizeVariables(lhsSBadVars);
	  qNorm.normalizeVariables(trm);
	  qDenorm.makeInverse(qNorm);
	  ASS_EQ(trm,qDenorm.apply(rNorm.apply(lhsSBadVars)));
	  rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
	} else {
	  rhsS=qr.substitution->applyToBoundResult(rhs);
	}

	if(ordering->compare(trm,rhsS)!=Ordering::GREATER) {
	  continue;
	}

	if(!simplPerformer->willPerform(qr.clause)) {
	  continue;
	}
	Literal* resLit = EqHelper::replace(lit,trm,rhsS);
	if(EqHelper::isEqTautology(resLit)) {
	  env.statistics->forwardDemodulationsToEqTaut++;
	  simplPerformer->perform(qr.clause, 0);
	  if(!simplPerformer->clauseKept()) {
	    return;
	  }
	}

	Inference* inf = new Inference2(Inference::FORWARD_DEMODULATION, cl, qr.clause);
	Unit::InputType inpType = (Unit::InputType)
		Int::max(cl->inputType(), qr.clause->inputType());

	Clause* res = new(cLen) Clause(cLen, inpType, inf);

	(*res)[0]=resLit;

	unsigned next=1;
	for(unsigned i=0;i<cLen;i++) {
	  Literal* curr=(*cl)[i];
	  if(curr!=lit) {
	    (*res)[next++] = curr;
	  }
	}
	ASS_EQ(next,cLen);

	res->setAge(cl->age());
	env.statistics->forwardDemodulations++;

	simplPerformer->perform(qr.clause, res);
	if(!simplPerformer->clauseKept()) {
	  return;
	}

      }
    }
  }
}

}
