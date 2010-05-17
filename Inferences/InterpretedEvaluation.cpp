/**
 * @file InterpretedEvaluation.cpp
 * Implements class InterpretedEvaluation.
 */

#include "../Lib/Exception.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "../Indexing/TermSharing.hpp"

#include "../Shell/Statistics.hpp"

#include "InterpretedEvaluation.hpp"

namespace Inferences
{
using namespace Lib;
using namespace Kernel;

/**
 * Return number of internal interpreting function that
 * interprets the top function of @b t. It the top function
 * of @b t is not interpreted, return -1.
 */
int InterpretedEvaluation::getInterpretedFunction(Term* t)
{
  CALL("InterpretedEvaluation::getInterpretedFunction");

  Signature::Symbol* sym =env.signature->getFunction(t->functor());
  if(!sym->interpreted() || sym->arity()==0) {
    return -1;
  }
  Signature::InterpretedSymbol* isym =
      static_cast<Signature::InterpretedSymbol*>(sym);
  return isym->getInterpretation();
}

/**
 * Return number of internal interpreting predicate that
 * interprets the predicate symbol of @b lit. It the predicate symbol
 * of @b lit is not interpreted, return -1.
 */
int InterpretedEvaluation::getInterpretedPredicate(Literal* lit)
{
  CALL("InterpretedEvaluation::getInterpretedPredicate");

  Signature::Symbol* sym =env.signature->getPredicate(lit->functor());
  if(!sym->interpreted()) {
    return -1;
  }
  Signature::InterpretedSymbol* isym =
      static_cast<Signature::InterpretedSymbol*>(sym);
  return isym->getInterpretation();
}

/**
 * Evaluate internal interpreted function number @b fnIndex on arguments
 * @b args and return resulting interpreted constant. If the evaluation
 * cannot be performed, return 0 and no simplification will occur.
 */
Term* InterpretedEvaluation::evaluateFunction(int fnIndex, TermList* args)
{
  CALL("InterpretedEvaluation::interpretFunction");
  ASS_GE(fnIndex, 0);

  Interpretation interp = static_cast<Interpretation>(fnIndex);
  ASS(Theory::isFunction(interp));

  InterpretedType arg1, arg2, arg3;

  switch(Theory::getArity(interp)) {
  case 3:
    arg3=theory->interpretConstant(args[2]);
  case 2:
    arg2=theory->interpretConstant(args[1]);
  case 1:
    arg1=theory->interpretConstant(args[0]);
  }

  InterpretedType res;

  //we do owerflow checking based on the fact that InterpretedType is int
  ASS_STATIC(sizeof(InterpretedType)==4);

  switch(interp) {
  case Theory::SUCCESSOR:
    if(arg1==INT_MAX) {
      return 0;
    }
    res=arg1+1;
    break;
  case Theory::UNARY_MINUS:
    if(!Int::safeUnaryMinus(arg1, res)) {
      return 0;
    }
    break;
  case Theory::PLUS:
    if(!Int::safePlus(arg1, arg2, res)) {
      return 0;
    }
    break;
  case Theory::MINUS:
    if(!Int::safeMinus(arg1, arg2, res)) {
      return 0;
    }
    break;
  case Theory::MULTIPLY:
  {
    if(!Int::safeMultiply(arg1, arg2, res)) {
      return 0;
    }
    break;
  }
  case Theory::DIVIDE:
    if(arg2==0 || arg1%arg2!=0) {
      return 0;
    }
    res=arg1/arg2;
    break;
  case Theory::IF_THEN_ELSE:
    if(arg1) {
      res=arg2;
    }
    else {
      res=arg3;
    }
    break;

  default:
    ASSERTION_VIOLATION;
  }

  return theory->getRepresentation(res);
}

bool InterpretedEvaluation::evaluatePredicate(int predIndex, TermList* args)
{
  CALL("InterpretedEvaluation::interpretPredicate");
  ASS_GE(predIndex, 0);

  Interpretation interp = static_cast<Interpretation>(predIndex);
  ASS(!Theory::isFunction(interp));


  //all interpreted predicates are binary
  ASS_EQ(Theory::getArity(interp), 2);
  InterpretedType arg1=theory->interpretConstant(args[0]);
  InterpretedType arg2=theory->interpretConstant(args[1]);

  switch(interp) {
  case Theory::EQUAL:
    return arg1==arg2;
  case Theory::GREATER:
    return arg1>arg2;
  case Theory::GREATER_EQUAL:
    return arg1>=arg2;
  case Theory::LESS:
    return arg1<arg2;
  case Theory::LESS_EQUAL:
    return arg1<=arg2;
  default:
    ASSERTION_VIOLATION;
  }
}

bool InterpretedEvaluation::simplifyLiteral(Literal* lit,
	bool& constant, Literal*& res, bool& constantTrue)
{
  CALL("InterpretedEvaluation::evaluateLiteral");

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<bool> allItpConsts(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  allItpConsts.push(true);
  toDo.push(lit->args());

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      bool childrenModified=modified.pop();
      bool allChildrenInterpreted=allItpConsts.pop();
      int itpFn=getInterpretedFunction(orig);

      if(!childrenModified && itpFn<0) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	allItpConsts.setTop(false);
	continue;
      }

      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      Term* newTrm=0;
      if(itpFn>=0 && allChildrenInterpreted) {
	newTrm=evaluateFunction(itpFn, argLst);
      }
      if(!newTrm && childrenModified) {
	newTrm=Term::create(orig,argLst);
	allItpConsts.setTop(false);
      }
      args.truncate(args.length() - orig->arity());
      if(newTrm) {
	args.push(TermList(newTrm));
	modified.setTop(true);
      }
      else {
	//we weren't able to simplify the term
	args.push(TermList(orig));
	allItpConsts.setTop(false);
      }
      continue;
    }

    toDo.push(tt->next());

    TermList tl=*tt;
    if(tl.isVar()) {
      args.push(tl);
      allItpConsts.setTop(false);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    if(theory->isInterpretedConstant(t)) {
      args.push(tl);
      continue;
    }

    terms.push(t);
    modified.push(false);
    allItpConsts.push(true);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  bool childrenModified=modified.pop();
  bool allChildrenInterpreted=allItpConsts.pop();
  int itpPred=getInterpretedPredicate(lit);


  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);

  if(itpPred>=0 && allChildrenInterpreted) {
    constant=true;
    constantTrue=lit->isNegative() ^ evaluatePredicate(itpPred, argLst);
    return true;
  }

  if(itpPred==Theory::GREATER_EQUAL || itpPred==Theory::LESS || itpPred==Theory::LESS_EQUAL) {
    //we want to transform all inequalities to GREATER
    //TODO: create a preprocessing rule for this
    unsigned grPred=env.signature->getInterpretingSymbol(Theory::GREATER);
    bool polarity=lit->polarity();
    if(itpPred==Theory::LESS_EQUAL || itpPred==Theory::GREATER_EQUAL) {
      polarity^=1;
    }
    if(itpPred==Theory::LESS || itpPred==Theory::GREATER_EQUAL) {
      swap(argLst[0], argLst[1]);
    }
    constant=false;
    res=Literal::create(grPred, 2, polarity, false, argLst);
    return true;
  }

  if(!childrenModified) {
    res=lit;
    return false;
  }

  constant=false;

  res=Literal::create(lit,argLst);
  return true;
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

//  LOG("orig: "<<(*cl));
//  LOG("res:  "<<(*res));

  return res;
}

}
