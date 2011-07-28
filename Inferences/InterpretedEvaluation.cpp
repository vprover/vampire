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
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Statistics.hpp"

#include "InterpretedEvaluation.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences
{
using namespace Lib;
using namespace Kernel;

/**
 * We use descendants of this class to evaluate various functions.
 *
 * One function can be evaluated only by one Evaluator object.
 */
class InterpretedEvaluation::Evaluator
{
public:
  virtual ~Evaluator() {}

  bool canEvaluateFunc(unsigned func)
  {
    CALL("InterpretedEvaluation::Evaluator::canEvaluateFunc");

    if(!theory->isInterpretedFunction(func)) {
      return false;
    }
    Interpretation interp = theory->interpretFunction(func);
    return canEvaluate(interp);
  }

  bool canEvaluatePred(unsigned pred)
  {
    CALL("InterpretedEvaluation::Evaluator::canEvaluatePred");

    if(!theory->isInterpretedPredicate(pred)) {
      return false;
    }
    Interpretation interp = theory->interpretPredicate(pred);
    return canEvaluate(interp);
  }

  virtual bool canEvaluate(Interpretation interp) = 0;

  virtual bool tryEvaluateFunc(Term* trm, Term*& res) { return false; }
  virtual bool tryEvaluatePred(Literal* trm, bool& res)  { return false; }
};

class InterpretedEvaluation::ConversionEvaluator : public Evaluator
{
public:
  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedEvaluation::ConversionEvaluator::canEvaluate");

    return theory->isConversionOperation(interp);
  }

  virtual bool tryEvaluateFunc(Term* trm, Term*& res)
  {
    CALL("InterpretedEvaluation::ConversionEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));
    LOG("conv eval trying "<<trm->toString());

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      ASS(theory->isConversionOperation(itp));
      ASS_EQ(theory->getArity(itp), 1);

      TermList argTrm = *trm->nthArgument(0);
      switch(itp) {
      case Theory::INT_TO_RAT:
      {
	IntegerConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	RationalConstantType resNum(arg,1);
	res = theory->representConstant(resNum);
	return true;
      }
      case Theory::INT_TO_REAL:
      {
	IntegerConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	RealConstantType resNum(RationalConstantType(arg,1));
	res = theory->representConstant(resNum);
	return true;
      }
      case Theory::RAT_TO_INT:
      {
	RationalConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	IntegerConstantType resNum = IntegerConstantType::floor(arg);
	res = theory->representConstant(resNum);
	return true;
      }
      case Theory::RAT_TO_REAL:
      {
	RationalConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	RealConstantType resNum(arg);
	res = theory->representConstant(resNum);
	return true;
      }
      case Theory::REAL_TO_INT:
      {
	RealConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	IntegerConstantType resNum = IntegerConstantType::floor(RationalConstantType(arg));
	res = theory->representConstant(resNum);
	return true;
      }
      case Theory::REAL_TO_RAT:
      {
	//this is correct only as long as we only represent rational real numbers
	RealConstantType arg;
	if(!theory->tryInterpretConstant(argTrm, arg)) { return false; }
	RationalConstantType resNum(arg);
	res = theory->representConstant(resNum);
	return true;
      }

      default:
	ASSERTION_VIOLATION;
      }
    }
    catch(ArithmeticException)
    {
      return false;
    }
  }
};

/**
 * Evaluates constant theory expressions
 */
template<class T>
class InterpretedEvaluation::TypedEvaluator : public Evaluator
{
public:
  typedef T Value;

  TypedEvaluator() {}

  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedEvaluation::TypedEvaluator::canEvaluate");

    if(!theory->hasSingleSort(interp)) { return false; } //there are other rules to evaluate equality

    unsigned opSort = theory->getOperationSort(interp);
    return opSort==T::getSort();
  }

  virtual bool tryEvaluateFunc(Term* trm, Term*& res)
  {
    CALL("InterpretedEvaluation::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if(arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      T resNum;
      TermList arg1Trm = *trm->nthArgument(0);
      T arg1;
      if(!theory->tryInterpretConstant(arg1Trm, arg1)) { return false; }
      if(arity==1) {
	if(!tryEvaluateUnaryFunc(itp, arg1, resNum)) { return false;}
      }
      else if(arity==2) {
	TermList arg2Trm = *trm->nthArgument(1);
	T arg2;
	if(!theory->tryInterpretConstant(arg2Trm, arg2)) { return false; }
	if(!tryEvaluateBinaryFunc(itp, arg1, arg2, resNum)) { return false;}
      }
      res = theory->representConstant(resNum);
      return true;
    }
    catch(ArithmeticException)
    {
      return false;
    }
  }

  virtual bool tryEvaluatePred(Literal* lit, bool& res)
  {
    ASS(theory->isInterpretedPredicate(lit));

    try {
      Interpretation itp = theory->interpretPredicate(lit);
      ASS(!theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if(arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      TermList arg1Trm = *lit->nthArgument(0);
      T arg1;
      if(!theory->tryInterpretConstant(arg1Trm, arg1)) { return false; }
      if(arity==1) {
	if(!tryEvaluateUnaryPred(itp, arg1, res)) { return false;}
      }
      else {
	TermList arg2Trm = *lit->nthArgument(1);
	T arg2;
	if(!theory->tryInterpretConstant(arg2Trm, arg2)) { return false; }
	if(!tryEvaluateBinaryPred(itp, arg1, arg2, res)) { return false;}
      }
      if(lit->isNegative()) {
	res = !res;
      }
      return true;
    }
    catch(ArithmeticException)
    {
      return false;
    }

  }
protected:

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const T& arg, T& res)
  { return false; }
  virtual bool tryEvaluateBinaryFunc(Interpretation op, const T& arg1, const T& arg2, T& res)
  { return false; }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const T& arg1, bool& res)
  { return false; }
  virtual bool tryEvaluateBinaryPred(Interpretation op, const T& arg1, const T& arg2, bool& res)
  { return false; }
};

class InterpretedEvaluation::IntEvaluator : public TypedEvaluator<IntegerConstantType>
{
protected:
  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedEvaluation::IntEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::INT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::INT_SUCCESSOR:
      res = arg+1;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedEvaluation::IntEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::INT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::INT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::INT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::INT_DIVIDE:
      res = arg1/arg2;
      return true;
    case Theory::INT_MODULO:
      res = arg1%arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedEvaluation::IntEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::INT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::INT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::INT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::INT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    case Theory::INT_DIVIDES:
      res = (arg1%arg2)==0;
      return true;
    default:
      return false;
    }
  }
};

class InterpretedEvaluation::RatEvaluator : public TypedEvaluator<RationalConstantType>
{
protected:
  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedEvaluation::RatEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::RAT_UNARY_MINUS:
      res = -arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedEvaluation::RatEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::RAT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::RAT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::RAT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::RAT_DIVIDE:
      res = arg1/arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedEvaluation::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::RAT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::RAT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::RAT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedEvaluation::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_IS_INT:
      res = arg1.isInt();
      return true;
    default:
      return false;
    }
  }
};

class InterpretedEvaluation::RealEvaluator : public TypedEvaluator<RealConstantType>
{
protected:
  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedEvaluation::RealEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::REAL_UNARY_MINUS:
      res = -arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedEvaluation::RealEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::REAL_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::REAL_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::REAL_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::REAL_DIVIDE:
      res = arg1/arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedEvaluation::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::REAL_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::REAL_LESS:
      res = arg1<arg2;
      return true;
    case Theory::REAL_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedEvaluation::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_IS_INT:
      res = arg1.isInt();
      return true;
    case Theory::REAL_IS_RAT:
      //this is true as long as we can evaluate only rational reals.
      res = true;
      return true;
    default:
      return false;
    }
  }

};

class InterpretedEvaluation::LiteralSimplifier :  private TermTransformer
{
public:
  LiteralSimplifier()
  {
    CALL("InterpretedEvaluation::LiteralSimplifier::LiteralSimplifier");
    _evals.push(new IntEvaluator());
    _evals.push(new RatEvaluator());
    _evals.push(new RealEvaluator());
    _evals.push(new ConversionEvaluator());

    _funEvaluators.ensure(0);
    _predEvaluators.ensure(0);

  }

  ~LiteralSimplifier()
  {
    CALL("InterpretedEvaluation::LiteralSimplifier::~LiteralSimplifier");

    while(_evals.isNonEmpty()) {
      delete _evals.pop();
    }
  }

  bool evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst)
  {
    CALL("InterpretedEvaluation::LiteralSimplifier::evaluate");

    resLit = TermTransformer::transform(lit);
    unsigned pred = resLit->functor();

    Evaluator* predEv = getPredEvaluator(pred);
    if(predEv) {
      if(predEv->tryEvaluatePred(resLit, resConst)) {
	LOGV(resConst);
	isConstant = true;
	return true;
      }
    }
    if(resLit!=lit) {
      isConstant = false;
      LOGV(*lit);
      LOGV(*resLit);
      return true;
    }
    return false;
  }

protected:
  typedef Stack<Evaluator*> EvalStack;

  virtual TermList transform(TermList trm)
  {
    CALL("InterpretedEvaluation::LiteralSimplifier::transform");

    if(!trm.isTerm()) { return trm; }
    Term* t = trm.term();
    unsigned func = t->functor();

    Evaluator* funcEv = getFuncEvaluator(func);
    if(funcEv) {
      Term* res;
      if(funcEv->tryEvaluateFunc(t, res)) {
	return TermList(res);
      }
    }
    return trm;
  }

  Evaluator* getFuncEvaluator(unsigned func)
  {
    CALL("InterpretedEvaluation::getFuncEvaluator");

    if(func>=_funEvaluators.size()) {
      unsigned oldSz = _funEvaluators.size();
      unsigned newSz = func+1;
      _funEvaluators.expand(newSz);
      for(unsigned i=oldSz; i<newSz; i++) {
	EvalStack::Iterator evit(_evals);
	while(evit.hasNext()) {
	  Evaluator* ev = evit.next();
	  if(ev->canEvaluateFunc(i)) {
	    ASS_EQ(_funEvaluators[i], 0); //we should have only one evaluator for each function
	    _funEvaluators[i] = ev;
	  }
	}
      }
    }
    return _funEvaluators[func];
  }

  Evaluator* getPredEvaluator(unsigned pred)
  {
    CALL("InterpretedEvaluation::getPredEvaluator");

    if(pred>=_predEvaluators.size()) {
      unsigned oldSz = _predEvaluators.size();
      unsigned newSz = pred+1;
      _predEvaluators.expand(newSz);
      for(unsigned i=oldSz; i<newSz; i++) {
	EvalStack::Iterator evit(_evals);
	while(evit.hasNext()) {
	  Evaluator* ev = evit.next();
	  if(ev->canEvaluatePred(i)) {
	    ASS_EQ(_predEvaluators[i], 0); //we should have only one evaluator for each predicate
	    _predEvaluators[i] = ev;
	  }
	}
      }
    }
    return _predEvaluators[pred];
  }

  EvalStack _evals;
  DArray<Evaluator*> _funEvaluators;
  DArray<Evaluator*> _predEvaluators;
};

InterpretedEvaluation::InterpretedEvaluation()
{
  CALL("InterpretedEvaluation::InterpretedEvaluation");

  _simpl = new LiteralSimplifier();
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
  LOG("Simplifying "<<cl->toString());

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
	env.statistics->evaluations++;
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
  env.statistics->evaluations++;

  LOG("Result: "<<res->toString());
  return res;
}

}
