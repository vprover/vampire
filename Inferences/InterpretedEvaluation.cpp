/**
 * @file InterpretedEvaluation.cpp
 * Implements class InterpretedEvaluation.
 */

#include "Lib/Exception.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Int.hpp"

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


InterpretedEvaluation::InterpretedEvaluation()
{
  CALL("InterpretedEvaluation::InterpretedEvaluation");

  _simpl = new InterpretedLiteralEvaluator();
}

InterpretedEvaluation::~InterpretedEvaluation()
{
  CALL("InterpretedEvaluation::~InterpretedEvaluation");

  delete _simpl;
}



bool InterpretedEvaluation::simplifyLiteral(Literal* lit,
	bool& constant, Literal*& res, bool& constantTrue)
{
  CALL("InterpretedEvaluation::evaluateLiteral");

  if(lit->arity()==0 || !lit->hasInterpretedConstants()) {
    //we have no interpreted predicates of zero arity
    return false;
  }

  return _simpl->evaluate(lit, constant, res, constantTrue);
}

Clause* InterpretedEvaluation::simplify(Clause* cl)
{
  CALL("InterpretedEvaluation::perform");

  TimeCounter tc(TC_INTERPRETED_EVALUATION);

  static DArray<Literal*> newLits(32);
  unsigned clen=cl->length();
  bool modified=false;
  newLits.ensure(clen);
  unsigned next=0;
  for(unsigned li=0;li<clen; li++) {
    Literal* lit=(*cl)[li];
    Literal* res;
    bool constant, constTrue;
    bool litMod=simplifyLiteral(lit, constant, res, constTrue);
    if(!litMod) {
      newLits[next++]=lit;
      continue;
    }
    modified=true;
    if(constant) {
      if(constTrue) {
	env -> statistics->evaluations++;
	LOG_TAUT("inf_ie",cl);
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

  int newLength = next;
  Inference* inf = new Inference1(Inference::EVALUATION, cl);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  for(int i=0;i<newLength;i++) {
    (*res)[i] = newLits[i];
  }

  res->setAge(cl->age());
  env -> statistics->evaluations++;

  LOG_SIMPL("inf_ie",cl,res);
  return res;
}

}
