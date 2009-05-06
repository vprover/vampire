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
  //TODO: implement

  //this is just a testing implementation
  if(t->functionName()=="f_plus") {
    return 0;
  }
  return -1;
}

/**
 * Return number of internal interpreting predicate that
 * interprets the predicate symbol of @b lit. It the predicate symbol
 * of @b lit is not interpreted, return -1.
 */
int InterpretedEvaluation::getInterpretedPredicate(Literal* lit)
{
  //TODO: implement
  return -1;
}

/**
 * Return number of interpreted function that is the top function of
 * @b t.
 */
bool InterpretedEvaluation::isInterpretedConstant(Term* t)
{
  //TODO: implement

  //this is just a testing implementation
  string fname=t->functionName();
  if(fname.substr(0,2)=="n_") {
    ASS_EQ(t->arity(),0);
    return true;
  }
  return false;
}

InterpretedType InterpretedEvaluation::interpretConstant(TermList t)
{
  ASS(t.isTerm());
  return interpretConstant(t.term());
}

InterpretedType InterpretedEvaluation::interpretConstant(Term* t)
{
  //TODO: implement

  //this is just a testing implementation
  ASS(isInterpretedConstant(t));
  string fname=t->functionName();
  int res;
  ALWAYS(Int::stringToInt(fname.substr(2,string::npos), res));
  return res;
}

Term* InterpretedEvaluation::getRepresentation(InterpretedType val)
{
  //TODO: implement

  //this is just a testing implementation
  string fname="n_"+Int::toString(val);
  int functor=env.signature->addFunction(fname, 0);

  Term* t = new(0) Term;
  t->makeSymbol(functor,0);
  return env.sharing->insert(t);
}


/**
 * Evaluate internal interpreted function number @b fnIndex on arguments
 * @b args and return resulting interpreted constant. If the evaluation
 * cannot be performed, return 0 and no simplification will occur.
 */
Term* InterpretedEvaluation::interpretFunction(int fnIndex, TermList* args)
{
  //TODO: implement

  //this is just a testing implementation
  if(fnIndex==0) {
    return getRepresentation(interpretConstant(args[0])+interpretConstant(args[1]));
  }
  INVALID_OPERATION("Unsupported interpreted function");
}

bool InterpretedEvaluation::interpretPredicate(int predIndex, TermList* args)
{
  INVALID_OPERATION("Unsupported interpreted predicate");
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
      if(!newTrm) {
	newTrm=Term::create(orig,argLst);
	allItpConsts.setTop(false);
      }
      args.truncate(args.length() - orig->arity());
      args.push(TermList(newTrm));
      modified.setTop(true);
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

void InterpretedEvaluation::perform(Clause* cl, bool& keep, ClauseIterator& toAdd,
	ClauseIterator& premises)
{
  CALL("InterpretedEvaluation::perform");

  premises=ClauseIterator::getEmpty();

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
	keep=false;
	toAdd=ClauseIterator::getEmpty();
	return;
      } else {
	continue;
      }
    }
    newLits[next++]=res;
  }
  if(!modified) {
    keep=true;
    toAdd=ClauseIterator::getEmpty();
    return;
  }

  int newLength = next;
  Inference* inf = new Inference1(Inference::EVALUATION, cl);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  for(int i=0;i<newLength;i++) {
    (*res)[i] = newLits[i];
  }

  res->setAge(cl->age()+1);
  env.statistics->evaluations++;

  keep=false;
  toAdd=pvi( getSingletonIterator(res) );
}

}
