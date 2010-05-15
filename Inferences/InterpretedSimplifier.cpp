/**
 * @file InterpretedSimplifier.cpp
 * Implements class InterpretedSimplifier.
 */

#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Theory.hpp"

#include "../Indexing/ArithmeticIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Shell/Statistics.hpp"

#include "InterpretedSimplifier.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class InterpretedSimplifier::ClauseSimplifier
{
private:
  ArithmeticIndex* _ai;

  Clause* cl;
  ForwardSimplificationPerformer* sperf;
  bool simplified;
  LiteralStack resLits;
  ConstraintDatabase localConstraints;
  Theory* theory;
public:
  bool deleted;
  ClauseStack premises;

  ClauseSimplifier(ArithmeticIndex* ai) : _ai(ai)
  {
    theory=Theory::instance();
  }

  struct LitProcOrderComparator
  {
    Comparison compare(Literal* l1, Literal* l2)
    {
      bool interp1=Theory::instance()->isInterpretedPredicate(l1);
      bool interp2=Theory::instance()->isInterpretedPredicate(l2);
      if(interp1 && !interp2) {
	return LESS;
      }
      if(!interp1 && interp2) {
	return GREATER;
      }
      if(!interp1) {
	return Int::compare(l1->weight(), l2->weight());
      }
      //all interpreted predicates are binary
      ASS_EQ(l1->arity(), 2);
      ASS_EQ(l2->arity(), 2);
      bool constArg1=Theory::instance()->isInterpretedConstant(*l1->nthArgument(0)) ||
	  Theory::instance()->isInterpretedConstant(*l1->nthArgument(1));
      bool constArg2=Theory::instance()->isInterpretedConstant(*l2->nthArgument(0)) ||
	  Theory::instance()->isInterpretedConstant(*l2->nthArgument(1));
      if(constArg1 && !constArg2) {
	return LESS;
      }
      if(!constArg1 && constArg2) {
	return GREATER;
      }
      return Int::compare(l1->weight(), l2->weight());
    }
  };

  bool simplify(Clause* clause, ForwardSimplificationPerformer* simplPerformer)
  {
    CALL("InterpretedSimplifier::ClauseSimplifier::simplify(Clause*)");

    cl=clause;
    sperf=simplPerformer;
    simplified=false;
    deleted=false;
    premises.reset();
    resLits.reset();
    localConstraints.reset();

    unsigned clen=cl->length();

    static DArray<Literal*> ordLits;
    ordLits.initFromArray(clen, *cl);
    ordLits.sort(LitProcOrderComparator());

    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      bool constant, constantTrue;
      Literal* slit;
      if(simplify(lit, constant, slit, constantTrue)) {
	simplified=true;
	if(constant) {
	  if(constantTrue) {
	    deleted=true;
	    return true;
	  }
	  else {
	    continue;
	  }
	}
	lit=slit;
      }
      localConstraints.handleLiteral(lit, true, 0, true);
      resLits.push(lit);
    }

    return simplified;
  }

  Clause* getResult()
  {
    CALL("InterpretedSimplifier::ClauseSimplifier::getResult");
    ASS(simplified);
    ASS(!deleted);

    Inference* inf;
    Unit::InputType it=cl->inputType();
    if(premises.isEmpty()) {
      inf=new Inference(Inference::EVALUATION);
    }
    else {
      UnitList* lst=0;
      while(premises.isNonEmpty()) {
	Clause* prem=premises.pop();
	UnitList::push(prem, lst);
	it=static_cast<Unit::InputType>(Int::max(it, prem->inputType()));
      }
      inf=new InferenceMany(Inference::EVALUATION, lst);
    }
    return Clause::fromIterator(LiteralStack::Iterator(resLits), it, inf);
  }

  bool simplify(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);
  bool simplifyFunction(Interpretation interp, TermList* args, TermList& res);


  bool removeEquivalentAdditionsAndSubtractionsFromOneSide(TermList& arg1, TermList& arg2);
  bool removeEquivalentAdditionsAndSubtractions(TermList& arg1, TermList& arg2);

  bool simplifyGreaterFromOneSide(TermList& arg1, TermList& arg2);

  bool simplifyPredicate(Interpretation interp, TermList* args, Literal* original,
      bool& constant, Literal*& res, bool& constantTrue);

  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise)
  {
    premise=0;
    if(theory->isInterpretedConstant(t)) {
      return val!=theory->interpretConstant(t);
    }
    if(localConstraints.isNonEqual(t, val, premise)) {
      if(!premise || sperf->willPerform(premise)) {
	return true;
      }
    }
    if(_ai->isNonEqual(t, val, premise)) {
      if(!premise || sperf->willPerform(premise)) {
	return true;
      }
    }
    return false;
  }
  bool isGreater(TermList t, InterpretedType val, Clause*& premise)
  {
    premise=0;
    if(theory->isInterpretedConstant(t)) {
      return theory->interpretConstant(t)>val;
    }
    if(localConstraints.isGreater(t, val, premise)) {
      if(!premise || sperf->willPerform(premise)) {
	return true;
      }
    }
    if(_ai->isGreater(t, val, premise)) {
      if(!premise || sperf->willPerform(premise)) {
	return true;
      }
    }
    return false;
  }

  void addPremise(Clause* premise)
  {
    if(premise) {
      premises.push(premise);
    }
  }

};

bool InterpretedSimplifier::ClauseSimplifier::simplifyFunction(Interpretation interp, TermList* args, TermList& res)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::simplifyFunction");
  ASS(Theory::isFunction(interp));

  Clause* premise;

  switch(interp) {
  case Theory::PLUS:
    if(args[0]==theory->zero()) {
      res=args[1];
      return true;
    }
    if(args[1]==theory->zero()) {
      res=args[0];
      return true;
    }
    break;
  case Theory::MINUS:
    if(args[1]==theory->zero()) {
      res=args[0];
      return true;
    }
    break;
  case Theory::MULTIPLY:
    if(args[0]==theory->one()) {
      res=args[1];
      return true;
    }
    if(args[1]==theory->one()) {
      res=args[0];
      return true;
    }
    break;
  case Theory::DIVIDE:
    if(args[1]==theory->one()) {
      res=args[0];
      return true;
    }
    if(args[0]==args[1] && isNonEqual(args[0], 0, premise)) {
      addPremise(premise);
      res=theory->one();
      return true;
    }
    break;
  case Theory::IF_THEN_ELSE:
    if(args[0]==theory->zero()) {
      res=args[2];
      return true;
    }
    if(args[0].isTerm() && theory->isInterpretedConstant(args[0].term())) {
      //if we had zero, we would have succeeded with the previous condition
      ASS_NEQ(theory->interpretConstant(args[0]), 0);
      res=args[1];
      return true;
    }
    break;
  default:;
  }

  return false;
}


bool InterpretedSimplifier::ClauseSimplifier::
  removeEquivalentAdditionsAndSubtractionsFromOneSide(TermList& arg1, TermList& arg2)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::removeEquivalentAdditionsAndSubtractionsFromOneSide");

  if(!arg1.isTerm()) {
    return false;
  }
  Term* t1=arg1.term();

  if(theory->isInterpretedFunction(t1, Theory::PLUS)) {
    if(*t1->nthArgument(0)==arg2) {
      //X+Y # X  ---> Y # 0
      arg1=*t1->nthArgument(1);
      arg2=theory->zero();
      return true;
    }
    if(*t1->nthArgument(1)==arg2) {
      //X+Y # Y  ---> X # 0
      arg1=*t1->nthArgument(0);
      arg2=theory->zero();
      return true;
    }
  }

  if(!arg2.isTerm()) {
    return false;
  }
  Term* t2=arg2.term();
  if(theory->isInterpretedFunction(t1, Theory::SUCCESSOR) && theory->isInterpretedConstant(t2)) {
    //s(X) # N ---> X # (N-1)
    InterpretedType t2Val=theory->interpretConstant(t2);
    if(t2Val!=INT_MIN) {
      arg1=*t1->nthArgument(0);
      arg2=TermList(theory->getRepresentation(t2Val-1));
      return true;
    }
  }


  return false;
}

/**
 * Remove addition and subtraction of equal values in given terms.
 * Return true iff any simplification was performed.
 *
 * Helps to simplify e.g. a+b>b+c into a>c.
 */
bool InterpretedSimplifier::ClauseSimplifier::
  removeEquivalentAdditionsAndSubtractions(TermList& arg1, TermList& arg2)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::removeEquivalentAdditionsAndSubtractions");

  bool res=false;

reevaluation:
  if(arg1==arg2 && arg1!=theory->zero()) {
    arg1=theory->zero();
    arg2=arg1;
    return true;
  }

  if(removeEquivalentAdditionsAndSubtractionsFromOneSide(arg1, arg2)) {
    res=true;
    goto reevaluation;
  }
  if(removeEquivalentAdditionsAndSubtractionsFromOneSide(arg2, arg1)) {
    res=true;
    goto reevaluation;
  }

  if(!arg1.isTerm() || !arg2.isTerm()) {
    return res;
  }
  Term* t1=arg1.term();
  Term* t2=arg2.term();
  if(t1->functor()!=t2->functor()) {
    return res;
  }
  if(theory->isInterpretedFunction(t1, Theory::PLUS)) {
    //X+Y # X+Z ---> Y # Z  (modulo commutativity)
    bool modified=true;
    if(*t1->nthArgument(0)==*t2->nthArgument(0)) {
      arg1=*t1->nthArgument(1);
      arg2=*t2->nthArgument(1);
    }
    else if(*t1->nthArgument(0)==*t2->nthArgument(1)) {
      arg1=*t1->nthArgument(1);
      arg2=*t2->nthArgument(0);
    }
    else if(*t1->nthArgument(1)==*t2->nthArgument(1)) {
      arg1=*t1->nthArgument(0);
      arg2=*t2->nthArgument(0);
    }
    else if(*t1->nthArgument(1)==*t2->nthArgument(0)) {
      arg1=*t1->nthArgument(0);
      arg2=*t2->nthArgument(1);
    }
    else {
      modified=false;
    }
    if(modified) {
      res=true;
      goto reevaluation;
    }
  }
  if(theory->isInterpretedFunction(t1, Theory::MINUS)) {
    if(*t1->nthArgument(1)==*t2->nthArgument(1)) {
      //X-Y # Z-Y ---> X # Z
      arg1=*t1->nthArgument(0);
      arg2=*t2->nthArgument(0);
      res=true;
      goto reevaluation;
    }
  }
  return res;
}

bool InterpretedSimplifier::ClauseSimplifier::simplifyGreaterFromOneSide(TermList& arg1, TermList& arg2)
{
  Clause* premise;
  Clause* premise2;

  if(arg1==theory->zero()) {
    if(theory->isInterpretedFunction(arg2)) {
      Interpretation itp=theory->interpretFunction(arg2.term());
      if(arg2.term()->arity()==2) {
        TermList arg21=*arg2.term()->nthArgument(0);
        TermList arg22=*arg2.term()->nthArgument(1);
        if(itp==Theory::MULTIPLY) {
          // X*Y>0 ---> Y>0 for X>0
          if(isGreater(arg21, 0, premise)) {
            arg2=arg22;
            addPremise(premise);
            return true;
          }
          if(isGreater(arg22, 0, premise)) {
            arg2=arg21;
            addPremise(premise);
            return true;
          }
        }
        else if(itp==Theory::DIVIDE) {
          // X/Y>0 ---> Y>0 for X>0 and Y!=0
          if(isGreater(arg21, 0, premise) && isNonEqual(arg22, 0, premise2)) {
            arg2=arg22;
            addPremise(premise);
            addPremise(premise2);
            return true;
          }
          // X/Y>0 ---> Y>0 for X>0
          if(isGreater(arg22, 0, premise)) {
            arg2=arg21;
            addPremise(premise);
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool InterpretedSimplifier::ClauseSimplifier::simplifyPredicate(Interpretation interp, TermList* args, Literal* original,
    bool& constant, Literal*& res, bool& constantTrue)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::simplifyPredicate");
  ASS(!Theory::isFunction(interp));

  Clause* premise;

  //all interpreted predicates are binary
  ASS_EQ(Theory::getArity(interp), 2);

  bool modified=false;

  switch(interp) {
  case Theory::EQUAL:
    if(removeEquivalentAdditionsAndSubtractions(args[0], args[1])) {
      modified=true;
    }
    break;
  case Theory::GREATER:
    if(theory->isInterpretedConstant(args[1])) {
      if(isGreater(args[0], theory->interpretConstant(args[1]), premise)) {
	// X>N ---> true if X>N
	addPremise(premise);
	constant=true;
	constantTrue=original->polarity();
	return true;
      }
    }
    if(theory->isInterpretedConstant(args[0])) {
      if(isGreater(args[1], theory->interpretConstant(args[0]), premise)) {
	// N>X ---> false if X>N
	addPremise(premise);
	constant=true;
	constantTrue=!original->polarity();
	return true;
      }
    }
    if(removeEquivalentAdditionsAndSubtractions(args[0], args[1])) {
      modified=true;
    }
    if(simplifyGreaterFromOneSide(args[0], args[1])) {
      modified=true;
    }
    if(simplifyGreaterFromOneSide(args[1], args[0])) {
      modified=true;
    }
    break;
  default:;
  }

  if(modified) {
    constant=false;
    res=Literal::create(original,args);
    return true;
  }

  return false;
}


bool InterpretedSimplifier::ClauseSimplifier::simplify(Literal* lit,
	bool& constant, Literal*& res, bool& constantTrue)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::simplify(Literal*)");

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
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
      bool isInterpreted=theory->isInterpretedFunction(orig);

      if(!childrenModified && !isInterpreted) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	continue;
      }

      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      Term* newTrm=0;
      if(isInterpreted) {
	Interpretation itp=theory->interpretFunction(orig);
	TermList sfRes;
	if(simplifyFunction(itp, argLst, sfRes)) {
	  args.truncate(args.length() - orig->arity());
	  args.push(sfRes);
	  modified.setTop(true);
	  continue;
	}
      }
      if(!newTrm && childrenModified) {
	newTrm=Term::create(orig,argLst);
      }
      args.truncate(args.length() - orig->arity());
      if(newTrm) {
	args.push(TermList(newTrm));
	modified.setTop(true);
      }
      else {
	//we weren't able to simplify the term
	args.push(TermList(orig));
      }
      continue;
    }

    toDo.push(tt->next());

    TermList tl=*tt;
    if(tl.isVar()) {
      args.push(tl);
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
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  bool childrenModified=modified.pop();
  bool isInterpreted=theory->isInterpretedPredicate(lit);

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);

  if(isInterpreted) {
    Interpretation itp=theory->interpretPredicate(lit);
    if(simplifyPredicate(itp, argLst, lit, constant, res, constantTrue)) {
      return true;
    }
  }

  if(childrenModified) {
    constant=false;
    res=Literal::create(lit,argLst);
    return true;
  }

  res=lit;
  return false;
}


///////////////////////////////////////

InterpretedSimplifier::InterpretedSimplifier()
{
}

InterpretedSimplifier::~InterpretedSimplifier()
{
}


void InterpretedSimplifier::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardDemodulation::attach");

  ForwardSimplificationEngine::attach(salg);

  _ai=static_cast<ArithmeticIndex*>(
	  _salg->getIndexManager()->request(ARITHMETIC_INDEX) );
  _simpl=new ClauseSimplifier(_ai);
}

void InterpretedSimplifier::detach()
{
  CALL("ForwardDemodulation::detach");

  delete _simpl;
  _simpl=0;

  _ai=0;
  _salg->getIndexManager()->release(ARITHMETIC_INDEX);

  ForwardSimplificationEngine::detach();
}


void InterpretedSimplifier::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("ForwardDemodulation::perform");

  if(!_simpl->simplify(cl, simplPerformer)) {
    return;
  }
  ClauseStack::Iterator premIt(_simpl->premises);
  while(premIt.hasNext()) {
    Clause* prem=premIt.next();
    if(!simplPerformer->willPerform(prem)) {
      return;
    }
  }

  env.statistics->interpretedSimplifications++;

  if(_simpl->deleted) {
    simplPerformer->perform(0, 0, 0);
  }
  else {
    Clause* res=_simpl->getResult();
    //we may pass zeroes for premisses only because we have forbidden use of
    //this rule together with backtracking splitting
    simplPerformer->perform(0, res, 0);
  }
}

}
















