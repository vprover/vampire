
/*
 * File InterpretedSimplifier.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file InterpretedSimplifier.cpp
 * Implements class InterpretedSimplifier.
 */

//TODO: replace GREATER by LESS_EQUAL, since that is the inequality predicate that the others are converted to

#include "Lib/Comparison.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Int.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"

#include "Indexing/ArithmeticIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "InterpretedSimplifier.hpp"

namespace Inferences
{

#if 0

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class InterpretedSimplifier::ClauseSimplifier
: public ArithmeticKB
{
private:
  ArithmeticIndex* _ai;
  Ordering* _ordering;

  Clause* cl;
  ForwardSimplificationPerformer* sperf;
  bool simplified;
  LiteralStack resLits;
  ConstraintDatabase localConstraints;
public:
  bool deleted;
  ClauseStack premises;

  ClauseSimplifier(ArithmeticIndex* ai) : _ai(ai)
  {
    _ordering=Ordering::instance();
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
	if(constant) {
	  simplified=true;
	  if(constantTrue) {
	    deleted=true;
	    return true;
	  }
	  else {
	    continue;
	  }
	}
	if(_ordering->compare(slit, lit)==Ordering::LESS) {
	  simplified=true;
	  lit=slit;
	}
      }
      localConstraints.handleLiteral(lit, true, 0, true);
      resLits.push(lit);
    }

    if(simplifySingletonVariables()) {
      simplified=true;
    }

    if(simplifyGreaterChains()) {
      simplified=true;
    }

    if(mergeSimpleVariableInequalities()) {
      simplified=true;
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
      inf=new Inference1(Inference::INTERPRETED_SIMPLIFICATION, cl);
    }
    else {
      UnitList* lst=0;
      UnitList::push(cl, lst);
      while(premises.isNonEmpty()) {
	Clause* prem=premises.pop();
	UnitList::push(prem, lst);
	it=static_cast<Unit::InputType>(Int::max(it, prem->inputType()));
      }
      inf=new InferenceMany(Inference::INTERPRETED_SIMPLIFICATION, lst);
    }
    return Clause::fromIterator(LiteralStack::Iterator(resLits), it, inf);
  }

  bool simplify(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);
  bool simplifyFunction(Interpretation interp, TermList* args, TermList& res);


  bool doEqualityAndInequalityEquivalentSimplificationsFromOneSide(TermList& arg1, TermList& arg2, bool equality);
  bool doEqualityAndInequalityEquivalentSimplifications(TermList& arg1, TermList& arg2, bool equality);

  bool simplifyPredicate(Interpretation interp, TermList* args, Literal* original,
      bool& constant, Literal*& res, bool& constantTrue);

  bool simplifyGreaterChains();
  bool simplifySingletonVariables();
  bool mergeSimpleVariableInequalities();

  /**
   * Take the topmost subterm of t that does not have a SUCCESSOR
   * function at the top, and decrease the @b queryValue appropriately.
   */
  void stripOffSuccessors(TermList& t, InterpretedType& queryValue)
  {
    TermList newT=t;
    int res=0;
    while(theory->isInterpretedFunction(newT, Theory::SUCCESSOR)) {
      newT=*newT.term()->nthArgument(0);
      res++;
    }

    int newVal;
    if(res && Int::safeMinus(queryValue,res,newVal)) {
      queryValue=newVal;
      t=newT;
    }
  }

  //overrides ArithmeticKB::isNonEqual
  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise)
  {
    CALL("isNonEqual");

    stripOffSuccessors(t, val);
    
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

  //overrides ArithmeticKB::isGreater
  bool isGreater(TermList t, InterpretedType val, Clause*& premise)
  {
    CALL("isGreater");

    stripOffSuccessors(t, val);

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

  //overrides ArithmeticKB::isLess
  bool isLess(TermList t, InterpretedType val, Clause*& premise)
  {
    CALL("isLess");

    stripOffSuccessors(t, val);

    premise=0;
    if(theory->isInterpretedConstant(t)) {
      return theory->interpretConstant(t)<val;
    }
    if(localConstraints.isLess(t, val, premise)) {
      if(!premise || sperf->willPerform(premise)) {
	return true;
      }
    }
    if(_ai->isLess(t, val, premise)) {
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

  switch(interp) {
  case Theory::UNARY_MINUS:
    if(theory->isInterpretedFunction(args[0], Theory::UNARY_MINUS)) {
      res=*args[0].term()->nthArgument(0);
      return true;
    }
    if(theory->isInterpretedFunction(args[0], Theory::MINUS)) {
      //-(X-Y) ---> Y-X
      TermList newArgs[2];
      newArgs[0]=*args[0].term()->nthArgument(1);
      newArgs[1]=*args[0].term()->nthArgument(0);
      unsigned minusFun=theory->getFnNum(Theory::MINUS);
      res=TermList(Term::create(minusFun, 2, newArgs));
      return true;
    }
    break;
  case Theory::PLUS:
    if(args[0]==theory->zero()) {
      res=args[1];
      return true;
    }
    if(args[1]==theory->zero()) {
      res=args[0];
      return true;
    }
    for(unsigned argIndex=0;argIndex<2;argIndex++) {
      if(theory->isInterpretedFunction(args[argIndex], Theory::UNARY_MINUS) && 
         args[1-argIndex]==*args[argIndex].term()->nthArgument(0) ) {
        //X+(-X) ---> 0
        res=theory->zero();
      }
      if(theory->isInterpretedFunction(args[argIndex], Theory::INT_QUOTIENT_E) && 
         theory->isInterpretedConstant(*args[argIndex].term()->nthArgument(1))) {
        //X+idiv(Y,N) --> idiv(X*N+Y,N) if X can be merged into Y (Y is a polynomial that contains a summand with term X)
        TermList divisorTerm=*args[argIndex].term()->nthArgument(1);
        InterpretedType divisor=theory->interpretConstant(divisorTerm);
        if(divisor!=0) {
          TermList newArgs[2];
          newArgs[0]=divisorTerm;
          newArgs[1]=args[1-argIndex];
          TermList mulTerm=TermList(Term::create(theory->getFnNum(Theory::MULTIPLY),2,newArgs));
          newArgs[0]=mulTerm;
          newArgs[1]=*args[argIndex].term()->nthArgument(0);
          TermList addTerm=TermList(Term::create(theory->getFnNum(Theory::PLUS),2,newArgs));
          
          Polynomial pol(addTerm);
          if(pol.mergeSummands()) {
            newArgs[0]=pol.toTerm();
            newArgs[1]=divisorTerm;
            res=TermList(Term::create(theory->getFnNum(Theory::INT_QUOTIENT_E),2,newArgs));
            return true;
          }
        }
      }
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
    for(unsigned argIndex=0;argIndex<2;argIndex++) {
      if(theory->isInterpretedConstant(args[1-argIndex]) && 
         theory->isInterpretedFunction(args[argIndex], Theory::DIVIDE) && 
         theory->isInterpretedConstant(*args[argIndex].term()->nthArgument(1)) ) {
        // N0*(Y/N1) ---> (N0/gcd(N0,N1))*(Y/(N1/gcd(N0,N1)))
        InterpretedType n1=theory->interpretConstant(args[1-argIndex]);
        InterpretedType n22=theory->interpretConstant(*args[argIndex].term()->nthArgument(1));
        TermList arg21=*args[argIndex].term()->nthArgument(0);
        InterpretedType argGcd=Int::gcd(n1,n22);
        if(argGcd!=1) {
          unsigned divFun=theory->getFnNum(Theory::DIVIDE);
          unsigned mulFun=theory->getFnNum(Theory::MULTIPLY);
          TermList newArg2Args[2];
          newArg2Args[0]=arg21;
          newArg2Args[1]=TermList(theory->getRepresentation(n22/argGcd));
          args[0]=TermList(theory->getRepresentation(n1/argGcd));
          args[1]=TermList(Term::create(divFun, 2, newArg2Args));
          res=TermList(Term::create(mulFun, 2, args));
          return true;
        }
      }
    }
    break;
  case Theory::DIVIDE:
    if(args[1]==theory->one()) {
      res=args[0];
      return true;
    }
    if(args[1]==theory->minusOne()) {
      // X/-1 --> -X
      res=TermList(Term::create(theory->getFnNum(Theory::UNARY_MINUS), 1, &args[0]));
      return true;
    }
    
    Clause* nonZeronessPremise;
    if(isNonEqual(args[1], 0, nonZeronessPremise)) {
      if(args[0]==args[1]) {
        addPremise(nonZeronessPremise);
        res=theory->one();
        return true;
      }
      if(theory->isInterpretedConstant(args[0]) && theory->isInterpretedConstant(args[1])) {
        // N1/N2 ---> (N1/gcd(N1,N2))/(N2/gcd(N1,N2))
        InterpretedType iarg1=theory->interpretConstant(args[0]);
        InterpretedType iarg2=theory->interpretConstant(args[1]);
        InterpretedType gcd=Int::gcd(iarg1,iarg2);
        if(gcd!=1) {
          iarg1/=gcd;
          iarg2/=gcd;
          if(iarg2==1) {
            res=TermList(theory->getRepresentation(iarg1));
          }
          else {
            TermList newArgs[2];
            newArgs[0]=TermList(theory->getRepresentation(iarg1));
            newArgs[1]=TermList(theory->getRepresentation(iarg2));
            unsigned divFun=theory->getFnNum(Theory::DIVIDE);
            res=TermList(Term::create(divFun, 2, newArgs));
          }
          
          addPremise(nonZeronessPremise);
          return true;
        }
      }
    }
    if(theory->isInterpretedConstant(args[1]) &&
       theory->isInterpretedFunction(args[0], Theory::MULTIPLY)) {
      for(unsigned argIndex=0;argIndex<2;argIndex++) {
        if(theory->isInterpretedConstant(*args[0].term()->nthArgument(argIndex)) ) {
          // (N0*Y)/N1 ---> (N0/gcd(N0,N1)*Y)/(N1/gcd(N0,N1))
          InterpretedType n11=theory->interpretConstant(*args[0].term()->nthArgument(argIndex));
          TermList arg12=*args[0].term()->nthArgument(1-argIndex);
          InterpretedType n2=theory->interpretConstant(args[1]);
          InterpretedType argGcd=Int::gcd(n11,n2);
          if(argGcd!=1) {
            unsigned divFun=theory->getFnNum(Theory::DIVIDE);
            unsigned mulFun=theory->getFnNum(Theory::MULTIPLY);
            TermList newArg2Args[2];
            newArg2Args[0]=TermList(theory->getRepresentation(n11/argGcd));
            newArg2Args[1]=arg12;
            args[0]=TermList(Term::create(mulFun, 2, newArg2Args));
            args[1]=TermList(theory->getRepresentation(n2/argGcd));
            res=TermList(Term::create(divFun, 2, args));
            return true;
          }
        }
      }
    }
    break;
  default:;
  }

//  Polynomial pol(TermList(Term::create(theory->getFnNum(interp), Theory::getArity(interp), args)));
//  if(pol.simplify()) {
//    res=pol.toTerm();
//    return true;
//  }

  return false;
}


bool InterpretedSimplifier::ClauseSimplifier::
  doEqualityAndInequalityEquivalentSimplificationsFromOneSide(TermList& arg1, TermList& arg2, bool equality)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::doEqualityAndInequalityEquivalentSimplificationsFromOneSide");

  Clause* premise;
  Clause* premise2;

  if(!arg1.isTerm()) {
    return false;
  }
  Term* t1=arg1.term();

  if(theory->isInterpretedFunction(t1, Theory::DIVIDE)) {
    TermList arg11=*t1->nthArgument(0);
    TermList arg12=*t1->nthArgument(1);
    if(equality) {
      if(isNonEqual(arg12,0, premise)) {
        //X/Y=Z ---> X=Y*Z if Y!=0
        arg1=arg11;
        unsigned mulFn=theory->getFnNum(Theory::MULTIPLY);
        TermList newArgs[2];
        newArgs[0]=arg12;
        newArgs[1]=arg2;
        arg2=TermList(Term::create(mulFn,2,newArgs));
        addPremise(premise);
        return true;
      }
    }
    else {
      if(isGreater(arg12,0, premise)) {
        //X/Y>Z ---> X>Y*Z if Y>0
        unsigned mulFn=theory->getFnNum(Theory::MULTIPLY);
        TermList newArgs[2];
        newArgs[0]=arg12;
        newArgs[1]=arg2;
        arg1=arg11;
        arg2=TermList(Term::create(mulFn,2,newArgs));
        addPremise(premise);
        return true;
      }
      if(isLess(arg12,0, premise)) {
        //X/Y>Z ---> Y*Z>X if Y<0
        unsigned mulFn=theory->getFnNum(Theory::MULTIPLY);
        TermList newArgs[2];
        newArgs[0]=arg12;
        newArgs[1]=arg2;
        arg1=arg11;
        arg2=TermList(Term::create(mulFn,2,newArgs));
        swap(arg1,arg2);
        addPremise(premise);
        return true;
      }
    }
  }

  if(!arg2.isTerm()) {
    return false;
  }
  Term* t2=arg2.term();

  if(arg1==theory->zero()) {
    if(theory->isInterpretedFunction(t2)) {
      Interpretation itp=theory->interpretFunction(t2);
      if(t2->arity()==2) {
        TermList arg21=*t2->nthArgument(0);
        TermList arg22=*t2->nthArgument(1);
        if(itp==Theory::MULTIPLY) {
          if(equality) {
            // X*Y=0 ---> Y=0 for X!=0
            if(isNonEqual(arg21, 0, premise)) {
              arg2=arg22;
              addPremise(premise);
              return true;
            }
            if(isNonEqual(arg22, 0, premise)) {
              arg2=arg21;
              addPremise(premise);
              return true;
            }
          }
          else {
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
            // X*Y>0 ---> 0>Y for X<0
            if(isLess(arg21, 0, premise)) {
              arg2=arg22;
              swap(arg1,arg2);
              addPremise(premise);
              return true;
            }
            if(isLess(arg22, 0, premise)) {
              arg2=arg21;
              swap(arg1,arg2);
              addPremise(premise);
              return true;
            }
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

/**
 * Perform equivalent simplifications on given RHS and LHS of an (in)equality.
 * Return true iff any simplification was performed.
 *
 * Helps to simplify e.g. a+b>b+c into a>c. If a simplification reversing the 
 * inequality sign is performed, arguments are swapped.
 */
bool InterpretedSimplifier::ClauseSimplifier::
  doEqualityAndInequalityEquivalentSimplifications(TermList& arg1, TermList& arg2, bool equality)
{
  CALL("InterpretedSimplifier::ClauseSimplifier::doEqualityAndInequalityEquivalentSimplifications");

  if(doEqualityAndInequalityEquivalentSimplificationsFromOneSide(arg1, arg2, equality)) {
    return true;
  }
  if(doEqualityAndInequalityEquivalentSimplificationsFromOneSide(arg2, arg1, equality)) {
    return true;
  }

  //merge both sides as polynomials and try to simplify them
  if(arg1==theory->zero()) {
    Polynomial pol(arg2);
    bool simplified=pol.simplify();
    
    simplified=pol.reduceCoeffitients()||simplified;
    if(simplified) {
      arg2=pol.toTerm();
      return true;
    }
  }
  else if(arg2==theory->zero()) {
    Polynomial pol(arg1);
    
    bool simplified=pol.simplify();
    simplified=pol.reduceCoeffitients()||simplified;
    if(simplified) {
      arg1=pol.toTerm();
      return true;
    }
  }
  else {
    Polynomial pol1(arg1);
    Polynomial pol2(arg2);
    pol1.subtract(pol2);
    
    bool simplified=pol1.simplify();
    simplified=pol1.reduceCoeffitients()||simplified;
    if(simplified) {
      arg1=pol1.toTerm();
      arg2=theory->zero();
      return true;
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
    for(unsigned argIndex=0;argIndex<2;argIndex++) {
      if(theory->isInterpretedConstant(args[argIndex])) {
        if(isNonEqual(args[1-argIndex], theory->interpretConstant(args[argIndex]), premise)) {
	  // X=N ---> false if X!=N
	  addPremise(premise);
	  constant=true;
	  constantTrue=!original->polarity();
	  return true;
        }
      }
    }
    if(doEqualityAndInequalityEquivalentSimplifications(args[0], args[1], true)) {
      modified=true;
    }
    break;
  case Theory::GREATER:
  case Theory::INT_GREATER:
    if(theory->isInterpretedConstant(args[1])) {
      if(isGreater(args[0], theory->interpretConstant(args[1]), premise)) {
	// X>N ---> true if X>N
	addPremise(premise);
	constant=true;
	constantTrue=original->polarity();
	return true;
      }
      if(isLess(args[0], theory->interpretConstant(args[1]), premise)) {
	// X>N ---> false if X<N
	addPremise(premise);
	constant=true;
	constantTrue=!original->polarity();
	return true;
      }
    }
    if(theory->isInterpretedConstant(args[0])) {
      if(isLess(args[1], theory->interpretConstant(args[0]), premise)) {
	// N>X ---> true if X<N
	addPremise(premise);
	constant=true;
	constantTrue=original->polarity();
	return true;
      }
      if(isGreater(args[1], theory->interpretConstant(args[0]), premise)) {
	// N>X ---> false if X>N
	addPremise(premise);
	constant=true;
	constantTrue=!original->polarity();
	return true;
      }
    }
    if(doEqualityAndInequalityEquivalentSimplifications(args[0], args[1], false)) {
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

  if(lit->arity()==0) {
    //we have no interpreted predicates of zero arity
    return false;
  }

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
	if(simplifyFunction(itp, argLst, sfRes) && _ordering->compare(sfRes,TermList(orig))==Ordering::LESS) {
//	if(simplifyFunction(itp, argLst, sfRes)) {
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
      if(constant || _ordering->compare(res, lit)==Ordering::LESS) {
        return true;
      }
    }
  }

  constant=false;
  if(childrenModified) {
    res=Literal::create(lit,argLst);
    return true;
  }

  res=lit;
  return false;
}

bool InterpretedSimplifier::ClauseSimplifier::simplifySingletonVariables()
{
  CALL("InterpretedSimplifier::ClauseSimplifier::simplifySingletonVariables");

  //remove X # Y   for # in {=,<=} and their negations (if Y is a variable that doesn't appear elsewhere)
  
  DHMultiset<unsigned> varOccurences;

  LiteralStack::Iterator lIt1(resLits);
  while(lIt1.hasNext()) {
    VariableIterator vit(lIt1.next());
    while(vit.hasNext()) {
      varOccurences.insert(vit.next().var());
    }
  }

  LiteralStack::Iterator lIt2(resLits);
  while(lIt2.hasNext()) {
    Literal* lit=lIt2.next();
    if(!theory->isInterpretedPredicate(lit)) {
      continue;
    }
    Interpretation itp=theory->interpretPredicate(lit);
    if(itp!=Theory::EQUAL && itp!=Theory::LESS_EQUAL) {
      continue;
    }
    bool shouldBeRemoved=false;
    for(unsigned argIndex=0;argIndex<2;argIndex++) {
      if(!lit->nthArgument(argIndex)->isVar()) {
        continue;
      }
      if(varOccurences.multiplicity(lit->nthArgument(argIndex)->var())==1) {
	shouldBeRemoved=true;
	break;
      }
    }
    if(shouldBeRemoved) {
      lIt2.del();
    }
  }
  
  return false;
}

bool InterpretedSimplifier::ClauseSimplifier::mergeSimpleVariableInequalities()
{
  CALL("InterpretedSimplifier::ClauseSimplifier::mergeSimpleVariableInequalities");

  //replace 0 # N1*X+P1 \/ 0 # -N2*X+P2  by 0 # N2*P1+N1*P2  for N1,N2>0 and # in {<,>,<=,>=,=,!=}
  //if X is a variable that doesn't appear elsewhere

  //TODO: implement

  DHMultiset<unsigned> varOccurences;

  LiteralStack::Iterator lIt1(resLits);
  while(lIt1.hasNext()) {
    VariableIterator vit(lIt1.next());
    while(vit.hasNext()) {
      varOccurences.insert(vit.next().var());
    }
  }

  typedef pair<Literal*, Polynomial*> LitData;
  DHMap<unsigned, pair<Literal*, Literal*> >  varPresence;



  return false;
}

bool InterpretedSimplifier::ClauseSimplifier::simplifyGreaterChains()
{
  CALL("InterpretedSimplifier::ClauseSimplifier::simplifyGreaterChains");
  
  //X>Y | Y>Z ---> X>Z  (if Y is variable that doesn't appear elsewhere)
  //X>Y | !(Z>Y) ---> !(Z>X)  (if Y is variable that doesn't appear elsewhere)
  
  typedef pair<Literal*, Literal*> LitPair;

  Stack<unsigned> vars;
  DHSet<unsigned> forbiddenVars;
  DHMap<unsigned,LitPair > varLits;
  
  vars.reset();
  forbiddenVars.reset();
  varLits.reset();
  
  LiteralStack::Iterator lIt1(resLits);
  while(lIt1.hasNext()) {
    Literal* l=lIt1.next();
    if(theory->isInterpretedPredicate(l, Theory::GREATER)) {
      for(unsigned argIndex=0;argIndex<2;argIndex++) {
        TermList arg=*l->nthArgument(argIndex);
        bool ok=false;
        if(arg.isVar()) {
          unsigned v=arg.var();
          if(!forbiddenVars.find(v)) {
            LitPair* lp;
            varLits.getValuePtr(v, lp, make_pair((Literal*)0,(Literal*)0));
            Literal** ltgt;
            Literal** lOther;
            if( (argIndex==0) ^ l->isPositive() ) {
              ltgt=&lp->first;
              lOther=&lp->second;
            }
            else {
              ltgt=&lp->second;
              lOther=&lp->first;
            }
            if(!*ltgt) {
              *ltgt=l;
              ok=true;
              if(*lOther) {
                vars.push(v);
              }
            }
          }
        }
        if(!ok) {
	  VariableIterator vit(arg);
	  while(vit.hasNext()) {
	    forbiddenVars.insert(vit.next().var());
	  }
        }
      }
    }
    else {
      VariableIterator vit(l);
      while(vit.hasNext()) {
        forbiddenVars.insert(vit.next().var());
      }
    }
  }
  while(vars.isNonEmpty()) {
    unsigned var=vars.pop();
    if(forbiddenVars.find(var)) {
      continue;
    }
    LitPair lp=varLits.get(var);
    ASS(lp.first);
    ASS(lp.second);
    if(lp.first->isNegative() && lp.second->isNegative()) {
      //we cannot safely merge the two literals if we have
      //!(X>Y) | !(Y>Z)
      continue;
    }
    bool neg=lp.first->isNegative() || lp.second->isNegative();
    unsigned firstArgIndex=lp.first->isPositive() ? 0 : 1;
    unsigned secondArgIndex=lp.second->isPositive() ? 1 : 0;
    ASS_EQ(lp.first->nthArgument(1-firstArgIndex)->var(), var);
    ASS_EQ(lp.second->nthArgument(1-secondArgIndex)->var(), var);
    
    unsigned gtPred=theory->getPredNum(Theory::GREATER);
    TermList args[2];
    args[0]=*lp.first->nthArgument(firstArgIndex);
    args[1]=*lp.second->nthArgument(secondArgIndex);
    if(neg) {
      swap(args[0],args[1]);
    }
    
    LiteralStack::Iterator lIt2(resLits);
    while(lIt2.hasNext()) {
      Literal* rlit=lIt2.next();
      if(rlit==lp.first || rlit==lp.second) {
        lIt2.del();
      }
    }
    
    Literal* newLit=Literal::create(gtPred, 2, !neg, false, args);
    resLits.push(newLit);
    return true;
  }
  
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

  if(cl->isFromPreprocessing() && cl->inputType()==Unit::AXIOM) {
    return;
  }
  
  TimeCounter tc(TC_INTERPRETED_SIMPLIFICATION);

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

  ClauseIterator premises=pvi( ClauseStack::Iterator(_simpl->premises) );

  if(_simpl->deleted) {
    simplPerformer->perform(premises, 0);
  }
  else {
    Clause* res=_simpl->getResult();
    simplPerformer->perform(premises, res);
  }
}

#endif

}
















