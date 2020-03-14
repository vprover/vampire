
/*
 * File ProxyElimination.cpp.
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
 * @file ProxyElimination.cpp
 *
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/LambdaElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"

#include "ProxyElimination.hpp"
#include <memory>

namespace Inferences {

typedef LambdaElimination LE;

ProxyElimination::ct_ptr ProxyElimination::isHolConstantApp(TermList tl, unsigned unaryBinaryOrTenary)
{
  CALL("ProxyElimination::isHolConstantApp(TermList ...)");
    
  ASS(unaryBinaryOrTenary > 0 && unaryBinaryOrTenary < 4);
  
  if(tl.isVar()){
    return 0;
  }

  ct_ptr cnst (new ConstantTerm());

  unsigned argnum=0;
  Signature::Symbol* sym = env.signature->getFunction(tl.term()->functor());
  
  while(sym->app()){
    argnum++;

    if(argnum > unaryBinaryOrTenary){ return 0; }

    cnst->args.push(*(tl.term()->nthArgument(3)));
    cnst->sorts.push(SortHelper::getArgSort(tl.term(), 3));

    tl = *(tl.term()->nthArgument(2));
    
    if(tl.isVar()){ return 0; }
    
    sym = env.signature->getFunction(tl.term()->functor());
  }

  if((argnum != unaryBinaryOrTenary) || (sym->proxy() == Signature::NOT_PROXY)){
    return 0;
  }
  
  ASS(cnst->args.size() == unaryBinaryOrTenary);
  cnst->constant = tl.term();
  cnst->prox = sym->proxy();
  return std::move(cnst);
}


ProxyElimination::ct_ptr ProxyElimination::isHolConstantApp(Literal* lit, unsigned unaryBinaryOrTenary)
{
  CALL("ProxyElimination::isHolConstantApp(Literal* ...)");
  
  //higher-order setting
  //ASS_REP(lit->isEquality(), lit->toString());
  if(!lit->isEquality()){ return 0; }

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);  
  
  ct_ptr cnst = isHolConstantApp(lhs, unaryBinaryOrTenary);
  if(cnst){
    cnst->onRight = 0;
    return std::move(cnst);
  }
  
  cnst = isHolConstantApp(rhs, unaryBinaryOrTenary);
  if(cnst){
    cnst->onRight = 1;
    return std::move(cnst);
  }  
  
  return 0;
}

Inference::Rule ProxyElimination::constToInfRule(Signature::Proxy cnst){
  CALL("ProxyElimination::constToInfRule");

  switch(cnst){
    case Signature::PI:
      return Inference::VPI_ELIMINATION;
    case Signature::SIGMA:
      return Inference::VSIGMA_ELIMINATION;
    case Signature::EQUALS:
      return Inference::HOL_EQUALITY_ELIMINATION;
    case Signature::NOT:
      return Inference::HOL_NOT_ELIMINATION;
    default:
      return Inference::BINARY_CONN_ELIMINATION;   
  }

}

TermList ProxyElimination::sigmaRemoval(TermList sigmaTerm, TermList expsrt){
  CALL("ProxyElimination::sigmaRemoval");

  static DHMap<unsigned,TermList> varSorts;
  varSorts.reset();

  if(sigmaTerm.isTerm()){
    VariableIterator2 vit(sigmaTerm.term());
    while(vit.hasNext()){
      pair<TermList, TermList> varTypePair = vit.next();
      if(!varSorts.find(varTypePair.first.var())){
        varSorts.insert(varTypePair.first.var(), varTypePair.second);
      }
    }
  }

  static Stack<TermList> argSorts;
  static Stack<TermList> termArgs;
  static Stack<TermList> args;
  argSorts.reset();
  termArgs.reset();
  args.reset();
 
  unsigned var;
  TermList varSort; 
  DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
  while(mapIt.hasNext()) {
    mapIt.next(var, varSort);
    if(varSort == Term::superSort()){
      args.push(TermList(var, false));
    } else {
      argSorts.push(varSort);
      termArgs.push(TermList(var, false));
    }
  }
  ASS(termArgs.size() == argSorts.size());

  VList* vl = VList::empty();
  for(int i = args.size() -1; i >= 0 ; i--){
    VList::push(args[i].var(), vl);
  }

  do{ 
    TermList resultSort = *expsrt.term()->nthArgument(0);
    TermList skSymSort = Term::arrowSort(argSorts, resultSort);
    unsigned fun = Skolem::addSkolemFunction(VList::length(vl), 0, skSymSort, vl);
    TermList head = TermList(Term::create(fun, args.size(), args.begin()));
    TermList skolemTerm = ApplicativeHelper::createAppTerm(skSymSort, head, termArgs);
    sigmaTerm = ApplicativeHelper::createAppTerm(expsrt, sigmaTerm, skolemTerm);
    expsrt = *expsrt.term()->nthArgument(1);
  }while(expsrt != Term::boolSort());   

  //cout << "OUT OF sigmaRemoval " + sigmaTerm.toString() << endl;

  return sigmaTerm;
}

TermList ProxyElimination::piRemoval(TermList piTerm, Clause* clause, TermList expsrt){
  
  CALL("ProxyElimination::piRemoval");

  unsigned maxVar = clause->maxVar();
  do{ 
    maxVar++;
    TermList newVar = TermList(maxVar, false);
    piTerm = ApplicativeHelper::createAppTerm(expsrt, piTerm, newVar);
    expsrt = *expsrt.term()->nthArgument(1);
  }while(expsrt != Term::boolSort()); 
  
  return piTerm;
}

/* returns 0 if t1 is a termList representing false, 1
   if it represents true and -1 otherwise.
 */
int ProxyElimination::isBoolValue(TermList tl){
  CALL("ProxyElimination::isBoolValue");
  
  if(!tl.isTerm()){ return -1;}
  if(env.signature->isFoolConstantSymbol(true, tl.term()->functor())){ return 1;}
  if(env.signature->isFoolConstantSymbol(false, tl.term()->functor())){ return 0;}
  
  return -1;
}


bool ProxyElimination::isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &applyPIrule, TermList &srt)
{
    CALL("ProxyElimination::isPISIGMAapp");
   
    ct_ptr cnst = isHolConstantApp(lit, 1);
    if(!cnst || (cnst->prox != Signature::PI && 
                 cnst->prox != Signature::SIGMA)){
      return false;
    }
   
    rhs = *lit->nthArgument(1 - cnst->onRight); 
    int rhsValue = isBoolValue(rhs);

    if(rhsValue < 0){ return false; }
    
    bool isPI = cnst->prox == Signature::PI;
    bool positive = rhsValue == lit->polarity();
    applyPIrule = (isPI && positive) || (!isPI && !positive);
  
    rhs = positive ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());

    t1 = cnst->args.pop();  
    TermList sigmaSrt = SortHelper::getResultSort(cnst->constant);
    srt = *sigmaSrt.term()->nthArgument(0);
    return true; 
}

bool ProxyElimination::isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, TermList &srt)
{
    CALL("ProxyElimination::isEQUALSApp");
   
    ct_ptr cnst = isHolConstantApp(lit, 2);
    if(!cnst || cnst->prox != Signature::EQUALS){return false;}
    
    TermList truthValue = *lit->nthArgument(1 - cnst->onRight); 

    int val = isBoolValue(truthValue);
    if(val < 0){return false; }
    else { positive = (val == lit->polarity()); }
  
    t1 = cnst->args.pop();
    t2 = cnst->args.pop();
    TermList equalSort = SortHelper::getResultSort(cnst->constant);
    srt = *equalSort.term()->nthArgument(0);
    return true; 
}

bool ProxyElimination::appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
  CALL("ProxyElimination::appOfORorIMPorAnd");

  ct_ptr cnst = isHolConstantApp(lit, 2);
  if(!cnst){return false;}

  TermList otherTerm = *lit->nthArgument(1 - cnst->onRight);
  int val = isBoolValue(otherTerm); 
  if(val < 0){ return false;}
   
  if((cnst->prox == Signature::AND) && ((val + lit->polarity()) % 2 == 0)){ return false;}
  if((cnst->prox == Signature::OR)  && ((val + lit->polarity()) % 2 == 1)){ return false;}  
  if((cnst->prox == Signature::IMP) && ((val + lit->polarity()) % 2 == 1)){ return false;}
  
  lhs1 = cnst->args.pop();
  lhs2 = cnst->args.pop();
  
  TermList troo = TermList(Term::foolTrue());
  TermList fals = TermList(Term::foolFalse());
   
  switch(cnst->prox){ 
  case Signature::AND:
    rhs1 = fals; rhs2 = fals; //rule for "and" is t1 = $false \/ t2 = $false ...
    return true;
  case Signature::OR:
    rhs1 = troo; rhs2 = troo;
    return true;
  case Signature::IMP:
    rhs1 = fals; rhs2 = troo;
    return true;
  default:
    return false;
  }

  return false;    
}


bool ProxyElimination::isNOTEquality(Literal* lit, TermList &newEqlhs, TermList &newEqrhs, bool &polarity)
{
    CALL("ProxyElimination::isNOTEquality");
    
    ct_ptr cnst = isHolConstantApp(lit, 1);
    if(!cnst || cnst->prox != Signature::NOT){ return false; }  
    
    newEqrhs = *lit->nthArgument(1 - cnst->onRight);
    newEqlhs = cnst->args.pop();
  
    int val = isBoolValue(newEqrhs);
    TermList boolValues[] = {TermList(Term::foolFalse()), TermList(Term::foolTrue())};
    
    if(val > -1){
      polarity = true;
      newEqrhs = lit->polarity() ? boolValues[1 - val] : boolValues[val]; //check this AYB
    }else{
      polarity = 1 - lit->polarity();
    }
    
    return true;
}

Clause* ProxyElimination::replaceLit2(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d, Literal* e)
{
    CALL("ProxyElimination::replaceLit2");

    int length = c->length();
    if(d){ length++;}
    if(e){ length++;}
    
    Clause* res = new(length) Clause(length, c->inputType(), inf);

    unsigned i = 0;
    while ((*c)[i] != a) { i++; }
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;
    if(d){(*res)[length - 1] = d;} 
    if(e){(*res)[length - 2] = e;}//adding new literals at differrent places...
    
    return res;
}

Clause* ProxyElimination::ORIMPANDRemovalISE::simplify(Clause* c)
  {
    CALL("ORIMPANDRemovalISE::simplify");
  
    //cout << "Attempting to simplify" + c->toString() << endl;

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      TermList lhs1, rhs1, lhs2, rhs2;
      Literal *lit = (*c)[i];
      if (appOfORorIMPorAND(lit, lhs1, rhs1, lhs2, rhs2)) {
        Literal* newLit1 = Literal::createEquality(true, lhs1, rhs1, Term::boolSort());
        Literal* newLit2 = Literal::createEquality(true, lhs2, rhs2, Term::boolSort());
        Clause* res = replaceLit2(c, lit, newLit1, new Inference1(Inference::BINARY_CONN_ELIMINATION, c), newLit2);
        res->setAge(c->age());
        //env.statistics->holORIMPANDsimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  }
 
Clause* ProxyElimination::ORIMPANDRemovalISE2::simplify(Clause* c)
{
  CALL("ORIMPANDRemovalISE2::simplify");   

  TermList subterm;
  TermList newTerm;
  unsigned literalPosition = 0;
  unsigned cLen = c->length();
  Inference* inference = new Inference1(Inference::BINARY_CONN_SHORT_CIRUCIT_EVAL, c);

  while(literalPosition < cLen){
    Literal *literal = (*c)[literalPosition];
  
    NonVariableNonTypeIterator nvi(literal);
    while (nvi.hasNext()) {
      subterm = nvi.next();

      ct_ptr cnst = isHolConstantApp(subterm, 2);
      if(cnst){
       int val = isBoolValue(cnst->args[1]);
       int val2 = isBoolValue(cnst->args[0]);
       switch(cnst->prox){
        case Signature::AND:
          if(val == 0 || val2 == 0){
            newTerm = TermList(Term::foolFalse());
            goto substitution; 
          }
          break;
        case Signature::OR:
          if(val == 1 || val2 == 1){ 
            newTerm = TermList(Term::foolTrue());
            goto substitution; 
          }
          break;
        case Signature::IMP:
          if(val == 0){ 
            newTerm = TermList(Term::foolTrue());
            goto substitution; 
          }
          break;
        default:
          break;          
       }         
      }
    }
    literalPosition++;
  }

  return c;
  
  substitution:

  Clause* conclusion = new(cLen) Clause(cLen, c->inputType(), inference);
  conclusion->setAge(c->age());

  // Copy the literals from the premise except for the one at `literalPosition`,
  for (unsigned i = 0; i < cLen; i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*c)[i], subterm, newTerm) : (*c)[i];
  }
  //env.statistics->holORIMPANDshortCircuitEval++;
  return conclusion;
  
}
 
Clause* ProxyElimination::NOTRemovalISE::simplify(Clause* c)
{
  CALL("NOTRemovalISE::simplify");
  
  int length = c->length();
  for (int i = length - 1; i >= 0; i--) {
    TermList lhs, rhs;
    bool polarity;
    Literal *lit = (*c)[i];
    if (isNOTEquality(lit, lhs, rhs, polarity)) {
      Literal *newLit;
      newLit = Literal::createEquality(polarity, lhs, rhs, Term::boolSort());//Check this in particular polarity, AYB
      Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::HOL_NOT_ELIMINATION, c));//Change inference AYB
      res->setAge(c->age());
      //env.statistics->holNOTsimplifications++;
      return res;
    }
  }

  // no literals of the form app(app(vOR... or app(app(vIMP... were found
  return c;
} 

Clause* ProxyElimination::EQUALSRemovalISE::simplify(Clause* c)
{
  CALL("EQUALSRemovalISE::simplify");

  int length = c->length();

  for (int i = length - 1; i >= 0; i--) {
    TermList lhs, rhs, sort;
    bool polarity;
    Literal *lit = (*c)[i];
    if (isEQUALSApp(lit, lhs, rhs, polarity, sort)) {
      Literal *newLit = Literal::createEquality(polarity, lhs, rhs, sort);//Check this in particular polarity, AYB
      Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::HOL_EQUALITY_ELIMINATION, c));//Change inference AYB
      res->setAge(c->age());
      //env.statistics->holEQAULSignatureimplifications++;
      //cout << "The premise is " + c->toString() << endl;
      //cout << "The conclusion is " + res->toString() << endl; 
      return res;
    }
  }

  // no literals of the form app(app(vOR... or app(app(vIMP... were found
  return c;
}   
 
Clause* ProxyElimination::PISIGMARemovalISE::simplify(Clause* c)
{
  CALL("PISIGMARemovalISE::simplify");

  int length = c->length();
  for (int i = length - 1; i >= 0; i--) {
    TermList t1, lhs, rhs, expsrt; 
    bool applyPIrule;
    Literal *lit = (*c)[i];
    if (isPISIGMAapp(lit, t1, rhs, applyPIrule, expsrt)) {
      Literal *newLit;
 
      if(applyPIrule){
        lhs = piRemoval(t1, c, expsrt);                  
      }else{
        lhs = sigmaRemoval(t1, expsrt);
      } 

      newLit = Literal::createEquality(true, lhs, rhs, Term::boolSort()); 

      Clause* res;
      if(applyPIrule){
        res = replaceLit2(c, lit, newLit, new Inference1(Inference::VPI_ELIMINATION, c));
      }else{
        res = replaceLit2(c, lit, newLit, new Inference1(Inference::VSIGMA_ELIMINATION, c));
      }           
      res->setAge(c->age());

      //env.statistics->holPISIGMAsimplifications++;
      return res;
    }
  }

  // no literals of the form app(app(vOR... or app(app(vIMP... were found
  return c;
} 


  
/*
 * Given a clause app(app(binConn, t1), t2) = boolval \/ A, this iterator
 * returns the clauses:
 * (1)  t1 = [~]boolval \/ [t2 = [~]boolval] \/ A 
 * (2)  t2 = [~]boolval \/ [t1 = [~]boolval] \/ A 
 * where [] defines an optional literal/connective that is included depending on the conn
 */
 
struct ProxyElimination::ProxyEliminationISE::ProxyEliminationIterator
{
  ProxyEliminationIterator(Clause *clause, Literal *lit)
    : _count(0),
      _lit(lit),
      _clause(clause),
      _pol(lit->polarity())
  {

    CALL("ProxyEliminationISE::ProxyEliminationIterator");
  
    ct_ptr cnst = isHolConstantApp(lit, 2);
    if (cnst) {     
           
      TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
      
      int val = isBoolValue(otherTermt);
      _rhsIsTrue = (val > -1) && ((unsigned)val == _pol);
      _rhsIsFalse = (val > -1) && ((unsigned)val != _pol);
      _rhsIsTerm = val < 0;
      _terms.push(cnst->args.pop());
      _terms.push(cnst->args.pop());
      _argSort = cnst->sorts.pop(); //only relevant for equality. All other sorts are bool.
      if(_rhsIsTerm){_terms.push(otherTermt);}
        
      _constant = cnst->prox; 
      
      switch(_constant){
        case Signature::OR:
        case Signature::IMP:
         if(_rhsIsTrue){ _count = 4; } //Iterator returns nothing
         break;
        case Signature::AND:
         if(_rhsIsFalse){ _count = 4; } //Iterator returns nothing
         break;
        case Signature::EQUALS:
         if(!_rhsIsTerm){ _count = 4; } //Iterator returns nothing
         break;
        default:
          break;
      }
    } else {
      cnst = isHolConstantApp(lit, 1);
      if(cnst && (cnst->prox == Signature::PI || cnst->prox == Signature::SIGMA)){
        TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
        if (isBoolValue(otherTermt) > -1){
          _count = 4;
        } else {
          _constant = cnst->prox; 
          _terms.push(cnst->args.pop());
          _terms.push(otherTermt);
          TermList sort = SortHelper::getResultSort(cnst->constant);
          _expsort = *sort.term()->nthArgument(0);
        }      
      }else{
        _count = 4; //Iterator returns nothing (Must be a better way of doing this!)
      }
    }
  }

  DECL_ELEMENT_TYPE(Clause *);

  bool hasNext() {  
     switch(_constant){
       case Signature::AND:
       case Signature::OR:
       case Signature::IMP:
         if(_rhsIsTerm){ return _count < 3; }
         break;
       case Signature::XOR:
       case Signature::IFF:
         if(_rhsIsTerm){ return _count < 4; }
         break;
       default:
         break;
     }
     return _count < 2;            
  }

  OWN_ELEMENT_TYPE next()
  {
    CALL("ProxyEliminationISE::proxyEliminationIterator::next()");

    TermList boolValues[] = {TermList(Term::foolTrue()), TermList(Term::foolFalse())};
  
    Clause *res;
    Inference *inf = new Inference1(constToInfRule(_constant), _clause);

    Literal* l1 = 0;
    Literal* l2 = 0;
    Literal* l3 = 0;      
  
    switch(_constant){
      case Signature::OR:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[1], Term::boolSort());
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Term::boolSort()) : 0; 
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[0], Term::boolSort());
          l2 = Literal::createEquality(true, _terms[1], boolValues[0], Term::boolSort());
          l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Term::boolSort());
        }       
        break;
      case Signature::AND:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[0], Term::boolSort()); 
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Term::boolSort()) : 0; 
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[1], Term::boolSort());
          l2 = Literal::createEquality(true, _terms[1], boolValues[1], Term::boolSort());
          l3 = Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Term::boolSort());
        }       
        break;        
      case Signature::IMP:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[_count], Term::boolSort());  
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Term::boolSort()) : 0;
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[1], Term::boolSort());
          l2 = Literal::createEquality(true, _terms[1], boolValues[0], Term::boolSort());
          l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Term::boolSort());           
        }
        break;
      case Signature::IFF:      
        if(_rhsIsTrue || (_rhsIsTerm && _count < 2)){
          l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Term::boolSort()); 
          l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Term::boolSort()); 
          l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Term::boolSort()) : 0; 
          break;          
        }
        if(_rhsIsFalse || (_rhsIsTerm && _count > 1)){
          l1 = Literal::createEquality(true, _terms[0], boolValues[_count % 2], Term::boolSort()); 
          l2 = Literal::createEquality(true, _terms[1], boolValues[_count % 2], Term::boolSort());             
          l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Term::boolSort()) : 0;
          break;
        }       
      case Signature::XOR:
        if(_rhsIsTrue || (_rhsIsTerm && _count < 2)){
          l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Term::boolSort()); 
          l2 = Literal::createEquality(true, _terms[1], boolValues[_count], Term::boolSort());         
          l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Term::boolSort()) : 0;
          break;
        }
        if(_rhsIsFalse || (_rhsIsTerm && _count > 1)){
          l1 = Literal::createEquality(true, _terms[0], boolValues[_count % 2], Term::boolSort()); 
          l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Term::boolSort());                
          l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Term::boolSort()) : 0; 
          break;  
        }
      case Signature::EQUALS:
         l1 = Literal::createEquality(_count, _terms[0], _terms[1], _argSort);
         l2 = Literal::createEquality(true, _terms[2], boolValues[(_count == _pol)], Term::boolSort());
         break;
      case Signature::PI:
         if(_count < 1){
           l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[0], Term::boolSort());
           l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Term::boolSort());
         }else{
           l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[1], Term::boolSort());
           l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Term::boolSort());          
         }
         break;
      case Signature::SIGMA:
         if(_count < 1){
           l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[0], Term::boolSort());
           l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Term::boolSort());
         }else{
           l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[1], Term::boolSort());
           l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Term::boolSort());
         }
         break;
      default:
        ASSERTION_VIOLATION;
    }
    
    if(l1 && l2 && l3){
      res = replaceLit2(_clause, _lit, l1, inf, l2, l3);
    }else if(l1 && l2){
      res = replaceLit2(_clause, _lit, l1, inf, l2);
    }else{
      res = replaceLit2(_clause, _lit, l1, inf);
    }
  
    _count++;
    
    
    /*if(_constant == Signature::IFF || _constant == Signature::OR || _constant == Signature::IMP){
      if(_count == 1){
        cout << "The original clause is: " + _clause->toString() << endl;
      }
      cout << "l1 is " + l1->toString() << endl;
      cout << "l2 is " + l2->toString() << endl;
    }*/

    //cout << "result is " + res->toString() << endl;
    res->setAge(_clause->age()+1);
    
    //env.statistics->holBINARYCONNgeneratingrules++;
    return res;
  }
private:
  TermList _expsort; //used for PI and SIGMA only.
  unsigned _count;
  Literal* _lit;
  Clause* _clause;
  unsigned _pol;
  bool _rhsIsTerm;
  bool _rhsIsTrue;
  bool _rhsIsFalse;
  TermList _argSort;
  TermStack _terms;
  Signature::Proxy _constant;
};

struct ProxyElimination::ProxyEliminationISE::ProxyEliminationFn
{
  ProxyEliminationFn(Clause* premise)
    : _premise(premise) {}
  DECL_RETURN_TYPE(VirtualIterator<Clause*>);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    CALL("ProxyEliminationISE::SubtermEqualityFn::operator()");

    return pvi(ProxyEliminationIterator(_premise, lit));
  }
private:
  Clause* _premise;
};

ClauseIterator ProxyElimination::ProxyEliminationISE::simplifyMany(Clause* c)
{
  CALL("ProxyEliminationISE::simplifyMany");

  auto it1 = Clause::Iterator(*c);
  auto it2 = getMappingIterator(it1, ProxyEliminationFn(c));
  auto it3 = getFlattenedIterator(it2);
  return pvi(it3);
}  
  
}
