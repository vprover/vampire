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
 * @file InterpretedEvaluation.cpp
 * Implements class InterpretedEvaluation.
 */

#include "Shell/Options.hpp"

#include "Lib/Exception.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Int.hpp"
#include "Kernel/Ordering.hpp" 
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Statistics.hpp"

#include "InterpretedEvaluation.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences
{
using namespace Lib;
using namespace Kernel;


InterpretedEvaluation::InterpretedEvaluation(bool doNormalize, Ordering& ordering) :
  _simpl(new InterpretedLiteralEvaluator(doNormalize))
{
  CALL("InterpretedEvaluation::InterpretedEvaluation");
}

InterpretedEvaluation::~InterpretedEvaluation()
{
  CALL("InterpretedEvaluation::~InterpretedEvaluation");

  delete _simpl;
}



bool InterpretedEvaluation::simplifyLiteral(Literal* lit,
	bool& constant, Literal*& res, bool& constantTrue,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedEvaluation::evaluateLiteral");

  if(lit->arity()==0) {
    //we have no interpreted predicates of zero arity
    return false;
  }

  bool okay = _simpl->evaluate(lit, constant, res, constantTrue,sideConditions);

  //if(okay && lit!=res){
  //  cout << "evaluate " << lit->toString() << " to " << res->toString() << endl;
  //}

  return okay;
}

Clause* InterpretedEvaluation::simplify(Clause* cl)
{
  CALL("InterpretedEvaluation::perform");
  try { 


    TimeCounter tc(TC_INTERPRETED_EVALUATION);

    /* do not evaluate theory axioms (both internal and external theory axioms)
     * Note: We want to skip the evaluation of internal theory axioms, because we already assume that
     *       internally added theory axioms are simplified as much as possible.
     *       We currently also skip externally added theory axioms. But by doing so we risk that we don't
     *       simplify simplifiable theory axioms, which were added by users unfamiliar with theorem proving.
     */
    if(cl->isTheoryAxiom()) return cl;


    static DArray<Literal*> newLits(32);
    unsigned clen=cl->length();
    bool modified=false;
    newLits.ensure(clen);
    unsigned next=0;
    Stack<Literal*> sideConditions;
    for(unsigned li=0;li<clen; li++) {
      Literal* lit=(*cl)[li];
      Literal* res;
      bool constant, constTrue;
      bool litMod=simplifyLiteral(lit, constant, res, constTrue,sideConditions);
      if(!litMod) {
        newLits[next++]=lit;
        continue;
      }
      modified=true;
      if(constant) {
        if(constTrue) {
          //cout << "evaluate " << cl->toString() << " to true" << endl;
          env.statistics->evaluationCnt++;
          return 0;
        } else {
          continue;
        }
      }
      
      newLits[next++]=res;
    }
    if(!modified) {
      return cl;
    }

    ASS(sideConditions.isEmpty())
    Stack<Literal*>::Iterator side(sideConditions);
    newLits.expand(clen+sideConditions.length());
    while(side.hasNext()){ newLits[next++]=side.next();}
    int newLength = next;
    Clause* res = new(newLength) Clause(newLength,SimplifyingInference1(InferenceRule::EVALUATION, cl));

    for(int i=0;i<newLength;i++) {
      (*res)[i] = newLits[i];
    }

    env.statistics->evaluationCnt++;
    return res; 

  } catch (MachineArithmeticException&) {
    /* overflow while evaluating addition, subtraction, etc. */
    return cl;
  }
}

}
