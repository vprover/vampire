/**
 * @file Polynomial.cpp
 * Implements class Polynomial.
 */

#include "../Lib/DHMultiset.hpp"
#include "../Lib/Int.hpp"

#include "Term.hpp"

#include "Polynomial.hpp"

namespace Kernel
{

Polynomial::Polynomial(TermList t0)
{
  CALL("Polynomial::Polynomian(TermList)");
  
  //pairs of inherited coefficients and terms to be interpreted
  static Stack<pair<InterpretedType,TermList> > toDo;
  
  toDo.push(make_pair(1,t0));
  
  while(toDo.isNonEmpty()) {
    InterpretedType coef=toDo.top().first;
    TermList t=toDo.top().second;
    toDo.pop();
    ASS(coef);
    
    bool handled=false;
    if(theory->isInterpretedFunction(t)) {
      Term* trm=t.term();
      Interpretation itp=theory->interpretFunction(t);
      switch(itp) {
      case Theory::PLUS:
        toDo.push(make_pair(coef, *trm->nthArgument(0)));
        toDo.push(make_pair(coef, *trm->nthArgument(1)));
        handled=true;
        break;
      case Theory::SUCCESSOR:
	_data.push(Summand(coef));
        toDo.push(make_pair(coef, *trm->nthArgument(0)));
        handled=true;
        break;
      case Theory::UNARY_MINUS:
      {
        InterpretedType newCoef;
        if(Int::safeUnaryMinus(coef, newCoef)) {
          toDo.push(make_pair(newCoef, *trm->nthArgument(0)));
          handled=true;
        }
        break;
      }
      case Theory::MINUS:
      {
        InterpretedType negCoef;
        if(Int::safeUnaryMinus(coef, negCoef)) {
          toDo.push(make_pair(coef, *trm->nthArgument(0)));
          toDo.push(make_pair(negCoef, *trm->nthArgument(1)));
          handled=true;
        }
        break;
      }
      case Theory::MULTIPLY:
      {
        for(unsigned argIndex=0;argIndex<2;argIndex++) {
          if(theory->isInterpretedConstant(*trm->nthArgument(argIndex))) {
            InterpretedType val=theory->interpretConstant(*trm->nthArgument(argIndex));
            InterpretedType newCoef;
            if(Int::safeMultiply(coef, val, newCoef)) {
              if(newCoef!=0) {
                TermList arg=*trm->nthArgument(1-argIndex);
                toDo.push(make_pair(newCoef, arg));
              }
              handled=true;
              break;
            }
          }
        }
        break;
      }
      default:;
      }
    }
    else if(theory->isInterpretedConstant(t)) {
      InterpretedType tVal=theory->interpretConstant(t);
      InterpretedType res;
      if(Int::safeMultiply(coef, tVal, res)) {
	_data.push(Summand(res));
	handled=true;
      }
    }
    if(!handled) {
      _data.push(Summand(coef, t));
    }
  }
}

void Polynomial::subtract(Polynomial& pol)
{
  CALL("Polynomial::subtract");
  
  SummandStack::Iterator ssit(pol._data);
  while(ssit.hasNext()) {
    Summand smd=ssit.next();
    InterpretedType newCoef;
    if(Int::safeUnaryMinus(smd.coef, newCoef)) {
      _data.push(Summand(newCoef, smd.term));
    }
    else {
      TermList negTrm;
      if(smd.term.isEmpty()) {
        negTrm=TermList(theory->minusOne());
      }
      else {
        negTrm=TermList(Term::create(theory->getFnNum(Theory::UNARY_MINUS), 1, &smd.term));
      }
      _data.push(Summand(smd.coef, negTrm));
    }
  }
}

bool Polynomial::simplify()
{
  CALL("Polynomial::simplify");

  return mergeSummands();
}

bool Polynomial::mergeSummands()
{
  CALL("Polynomial::mergeSummands");
  
  DHMultiset<TermList> occurences;
  SummandStack::Iterator ssit(_data);
  while(ssit.hasNext()) {
    occurences.insert(ssit.next().term);
  }
  
  static DHMap<TermList, InterpretedType> coefs;
  static Stack<TermList> merged;
  
  coefs.reset();
  merged.reset();
  
  bool mergesDone=false;
  
  SummandStack::Iterator ssit2(_data);
  while(ssit2.hasNext()) {
    Summand smd=ssit2.next();
    if(occurences.multiplicity(smd.term)) {
      InterpretedType* pcoef;
      if(coefs.getValuePtr(smd.term, pcoef)) {
        *pcoef=smd.coef;
        merged.push(smd.term);
      }
      else {
        InterpretedType newCoef;
        if(!Int::safePlus(*pcoef, smd.coef, newCoef)) {
          continue;
        }
        *pcoef=newCoef;
        mergesDone=true;
      }
      ssit2.del();
    }
  }
  
  while(merged.isNonEmpty()) {
    TermList trm=merged.pop();
    _data.push(Summand(coefs.get(trm), trm));
  }
  return mergesDone;
}

/**
 * Divide all summands in the polynomial by the GCD of their coeffitients.
 *
 * This is not a simplification, it changes the value of the polynomial.
 * The GCD used for reduction of summands is always positive.
 */
bool Polynomial::reduceCoeffitients()
{
  CALL("Polynomial::reduceCoeffitients");

  SummandStack::Iterator sit(_data);
  InterpretedType coefGcd=0;
  while(sit.hasNext()) {
    InterpretedType coef=sit.next().coef;
    if(coef==0) {
      continue;
    }
    if(coefGcd==0) {
      coefGcd=abs(coef);
    }
    else {
      coefGcd=Int::gcd(coefGcd, coef);
    }
  }
  if(coefGcd==0) {
    return false;
  }
  ASS_G(coefGcd,0);
  if(coefGcd==1) {
    return false;
  }
  size_t len=_data.size();
  for(size_t i=0;i<len;i++) {
    _data[i].coef/=coefGcd;
  }
  return true;
}

/**
 * Multiply all coeffitients by -1, return true iff successful.
 * Do not modify the polynomial if unsuccessful.
 */
bool Polynomial::negate()
{
  CALL("Polynomial::negate");
  
  size_t len=_data.size();
  for(size_t i=0;i<len;i++) {
    InterpretedType newCoef;
    if(!Int::safeUnaryMinus(_data[i].coef, newCoef)) {
      return false;
    }
  }
  for(size_t i=0;i<len;i++) {
    InterpretedType newCoef;
    ALWAYS(Int::safeUnaryMinus(_data[i].coef, newCoef));
    _data[i].coef=newCoef;
  }
  return true;
}

/**
 * Return true if all summands are either interpreted constants 
 * or contain constant functions as terms.
 */
bool Polynomial::isProperLinearPolynomial()
{
  CALL("Polynomial::isProperLinearPolynomial");

  size_t len=_data.size();
  for(size_t i=0;i<len;i++) {
    TermList trm=_data[i].term;
    if(!trm.isEmpty() && (!trm.isTerm() || trm.term()->arity()!=0)) {
      return false;
    }
  }
  return true;
}

TermList Polynomial::toTerm()
{
  CALL("Polynomial::toTerm");
  
  if(_data.isEmpty()) {
    return TermList(theory->getRepresentation(0));
  }
  unsigned plusFn=theory->getFnNum(Theory::PLUS);
  TermList res=_data.pop().toTerm();
  while(_data.isNonEmpty()) {
    TermList args[2];
    args[0]=_data.pop().toTerm();
    args[1]=res;
    res=TermList(Term::create(plusFn, 2, args));
  }
  return res;
}

TermList Polynomial::Summand::toTerm()
{
  CALL("Polynomial::toTerm");
  
  if(constant || coef==0) {
    return TermList(theory->getRepresentation(coef));
  }
  if(coef==1) {
    return term;
  }
  if(coef==-1) {
    return TermList(Term::create(theory->getFnNum(Theory::UNARY_MINUS), 1, &term));
  }
  TermList args[2];
  args[0]=TermList(theory->getRepresentation(coef));
  args[1]=term;
  return TermList(Term::create(theory->getFnNum(Theory::MULTIPLY), 2, args));
}


}
