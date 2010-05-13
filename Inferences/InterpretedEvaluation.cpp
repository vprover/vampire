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

enum ItpFunctionNumbers {
  ADD=0
};

/**
 * Return number of internal interpreting function that
 * interprets the top function of @b t. It the top function
 * of @b t is not interpreted, return -1.
 */
int InterpretedEvaluation::getInterpretedFunction(Term* t)
{
  CALL("InterpretedEvaluation::getInterpretedFunction");

  Signature::Symbol* sym =env.signature->getFunction(t->functor());
  if(!sym->interpreted()) {
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
 * Return number of interpreted function that is the top function of
 * @b t.
 */
bool InterpretedEvaluation::isInterpretedConstant(Term* t)
{
  CALL("InterpretedEvaluation::isInterpretedConstant");

  return t->arity()==0 && env.signature->getFunction(t->functor())->interpreted();
}

InterpretedType InterpretedEvaluation::interpretConstant(TermList t)
{
  CALL("InterpretedEvaluation::interpretConstant");

  ASS(t.isTerm());
  return interpretConstant(t.term());
}

InterpretedType InterpretedEvaluation::interpretConstant(Term* t)
{
  CALL("InterpretedEvaluation::interpretConstant");
  ASS(isInterpretedConstant(t));

  Signature::InterpretedSymbol* sym =
      static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(t->functor()));

  return sym->getValue();
}

Term* InterpretedEvaluation::getRepresentation(InterpretedType val)
{
  CALL("InterpretedEvaluation::getRepresentation");

  Term** pRes;

  if(!_constants.getValuePtr(val, pRes)) {
    return *pRes;
  }

  int functor=env.signature->addInterpretedConstant(val);

  Term* t = new(0) Term;
  t->makeSymbol(functor,0);
  *pRes=env.sharing->insert(t);
  return *pRes;
}


/**
 * Evaluate internal interpreted function number @b fnIndex on arguments
 * @b args and return resulting interpreted constant. If the evaluation
 * cannot be performed, return 0 and no simplification will occur.
 */
Term* InterpretedEvaluation::interpretFunction(int fnIndex, TermList* args)
{
  CALL("InterpretedEvaluation::interpretFunction");
  ASS_GE(fnIndex, 0);

  Interpretation interp = static_cast<Interpretation>(fnIndex);
  ASS(Theory::isFunction(interp));

  InterpretedType arg1, arg2, arg3;

  switch(Theory::getArity(interp)) {
  case 3:
    arg3=interpretConstant(args[2]);
  case 2:
    arg2=interpretConstant(args[1]);
  case 1:
    arg1=interpretConstant(args[0]);
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
    res=-arg1;
    if(res==arg1) {
      //the overflow at INT_MIN manifests by the value staying
      //the same for unary minus
      return 0;
    }
    break;
  case Theory::PLUS:
    if(arg2<0) {
      if(INT_MIN - arg2 > arg1) { return 0; }
    }
    else {
      if(INT_MAX - arg2 < arg1) { return 0; }
    }
    res=arg1+arg2;
    break;
  case Theory::MINUS:
    if(arg2<0) {
      if(INT_MIN + arg2 < arg1) { return 0; }
    }
    else {
      if(INT_MAX + arg2 > arg1) { return 0; }
    }
    res=arg1-arg2;
    break;
  case Theory::MULTIPLY:
  {
    ASS_STATIC(sizeof(long long)==8);
    long long mres=static_cast<long long>(arg1)*arg2;
    if(mres>INT_MAX || mres<INT_MIN) {
      return 0;
    }
    res=mres;
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

  return getRepresentation(res);
}

bool InterpretedEvaluation::interpretPredicate(int predIndex, TermList* args)
{
  CALL("InterpretedEvaluation::interpretPredicate");
  ASS_GE(predIndex, 0);

  Interpretation interp = static_cast<Interpretation>(predIndex);
  ASS(!Theory::isFunction(interp));


  //all interpreted predicates are binary
  ASS_EQ(Theory::getArity(interp), 2);
  InterpretedType arg1=interpretConstant(args[0]);
  InterpretedType arg2=interpretConstant(args[1]);

  switch(interp) {
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

bool InterpretedEvaluation::evaluateLiteral(Literal* lit,
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
      int itpFn=allChildrenInterpreted ? getInterpretedFunction(orig) : -1;

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
      if(itpFn>=0) {
	newTrm=interpretFunction(itpFn, argLst);
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
    if(isInterpretedConstant(t)) {
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
  int itpPred=allChildrenInterpreted ? getInterpretedPredicate(lit) : -1;

  if(!childrenModified && itpPred<0) {
    res=lit;
    return false;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);

  if(itpPred>=0) {
    constant=true;
    constantTrue=lit->isNegative() ^ interpretPredicate(itpPred, argLst);
    return true;
  }

  constant=false;
  res=Literal::create(static_cast<Literal*>(lit),argLst);
  return true;
}

Clause* InterpretedEvaluation::simplify(Clause* cl)
{
  CALL("InterpretedEvaluation::perform");

  static DArray<Literal*> newLits(32);
  unsigned clen=cl->length();
  bool modified=false;
  newLits.ensure(clen);
  unsigned next=0;
  for(unsigned li=0;li<clen; li++) {
    Literal* lit=(*cl)[li];
    Literal* res;
    bool constant, constTrue;
    bool litMod=evaluateLiteral(lit, constant, res, constTrue);
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
