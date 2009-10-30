/**
 * @file ForwardLiteralRewriting.cpp
 * Implements class ForwardLiteralRewriting.
 */

#include "../Lib/Int.hpp"

#include "../Kernel/Inference.hpp"
#include "../Kernel/Ordering.hpp"

#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "ForwardLiteralRewriting.hpp"

namespace Inferences
{

void ForwardLiteralRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardLiteralRewriting::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<RewriteRuleIndex*>(
	  _salg->getIndexManager()->request(REWRITE_RULE_SUBST_TREE) );
}

void ForwardLiteralRewriting::detach()
{
  CALL("ForwardLiteralRewriting::detach");
  _index=0;
  _salg->getIndexManager()->release(REWRITE_RULE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


void ForwardLiteralRewriting::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("ForwardLiteralRewriting::perform");

  static Ordering* ordering=Ordering::instance();

  TimeCounter tc(TC_FORWARD_LITERAL_REWRITING);

  unsigned clen=cl->length();

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    SLQueryResultIterator git=_index->getGeneralizations(lit, lit->isNegative(), true);
    while(git.hasNext()) {
      SLQueryResult qr=git.next();
      Clause* counterpart=_index->getCounterpart(qr.clause);

      if(cl==qr.clause || cl==counterpart) {
	continue;
      }

      Literal* rhs0 = (qr.literal==(*qr.clause)[0]) ? (*qr.clause)[1] : (*qr.clause)[0];
      Literal* rhs = lit->isNegative() ? rhs0 : Literal::oppositeLiteral(rhs0);

      ASS(qr.substitution->isIdentityOnQueryWhenResultBound());

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.literal
      ASS(qr.literal->containsAllVariablesOf(rhs));
      Literal* rhsS=qr.substitution->applyToBoundResult(rhs);

      if(ordering->compare(lit, rhsS)!=Ordering::GREATER) {
	continue;
      }

      if(!simplPerformer->willPerform(qr.clause) || !simplPerformer->willPerform(counterpart)) {
	continue;
      }

      Clause* premise=lit->isNegative() ? qr.clause : counterpart;

      Inference* inf = new Inference2(Inference::FORWARD_LITERAL_REWRITING, cl, premise);
      Unit::InputType inpType = (Unit::InputType)
	Int::max(cl->inputType(), premise->inputType());

      Clause* res = new(clen) Clause(clen, inpType, inf);

      (*res)[0]=rhsS;

      unsigned next=1;
      for(unsigned i=0;i<clen;i++) {
	Literal* curr=(*cl)[i];
	if(curr!=lit) {
	  (*res)[next++] = curr;
	}
      }
      ASS_EQ(next,clen);

      res->setAge(cl->age());
      env.statistics->forwardLiteralRewrites++;

      simplPerformer->perform(premise, res);
      if(!simplPerformer->clauseKept()) {
	return;
      }

    }
  }


}

};
