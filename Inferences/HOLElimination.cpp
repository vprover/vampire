
/*
 * File HOLElimination.cpp.
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
 * @file HOLElimination.cpp
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

#include "Shell/Statistics.hpp"
#include "Shell/BetaReductionEngine.hpp"
#include "Shell/FOOLElimAlt.hpp"

#include "HOLElimination.hpp"
#include <memory>

namespace Inferences {

unique_ptr<ConstantTerm> isHolConstantEquality(Literal* lit)
{
  CALL("isHolConstantEquality(Literal* lit)");
  
  if(!lit->isEquality()){ return NULL; }
  
  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);  
  
  unique_ptr<ConstantTerm> cnst = isHolConstantTerm(lhs);
  if(cnst){
    cnst->onRight = 0;
    return std::move(cnst);
  }
  
  cnst = isHolConstantTerm(rhs);
  if(cnst){
    cnst->onRight = 1;
    return std::move(cnst);
  }  
  
  return NULL;
  
}

unique_ptr<ConstantTerm> isHolConstantTerm(TermList tl)
{
  CALL("isHolConstantTerm(TermList tl)");
  
  unique_ptr<ConstantTerm> cnst (new ConstantTerm());
  
  if(tl.isTerm() && !tl.term()->hasVarHead()){
    Term* t = tl.term();
    SigSym* sym = env.signature->getFunction(t->functor());
    if(sym->hoLogicalConn() != SigSym::NULL_CONSTANT){
      cnst->cnst = sym->hoLogicalConn();
      switch(cnst->cnst){
        case SigSym::PI:
        case SigSym::SIGMA:
        case SigSym::NOT:
          cnst->arg1 = *t->nthArgument(0);
          break;
        default:
          cnst->arg1 = *t->nthArgument(0);
          cnst->arg2 = *t->nthArgument(1);
      }
      cnst->cnstTerm = t;
      return std::move(cnst);
    }
  }
  
  return NULL;
}
                

TermList sigmaRemoval(TermList sigmaTerm, unsigned expsrt){
 
  CALL("HOLElimination::sigmaRemoval"); 
  
  ASS(sigmaTerm.isTerm());
  ASS(env.signature->getFunction(sigmaTerm.term()->functor())->lambda());
    
  Stack<unsigned> sorts;
  Formula::VarList* vars = sigmaTerm.freeVariables();
  Formula::VarList::Iterator fvi(vars);
  DHMap<unsigned,unsigned> _varSorts;
  SortHelper::collectVariableSorts(sigmaTerm.term(), _varSorts);
  while (fvi.hasNext()) {
    unsigned var = (unsigned)fvi.next();
    sorts.push(_varSorts.get(var));
  }
  fvi.reset(vars);  
  unsigned arity = (unsigned)sorts.size();
      
  do{ 
    unsigned srt2 = env.sorts->getFuncSort(expsrt)->getDomainSort();         
     
    Stack<TermList> args(arity);
    if(arity){
      unsigned count = 0;
      while(fvi.hasNext()){
        unsigned sort = sorts[count];
        unsigned var = (unsigned)fvi.next();
        if(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::FUNCTION)){
          ASS_G(var, Term::VARIABLE_HEAD_LOWER_BOUND);
          Stack<TermList> dummy;
          args.push(FOOLElimAlt::etaExpand(var, FOOLElimAlt::toType(sort), false, dummy));
        }else{
          args.push(TermList(var, false));  
        }        
        count++;
        ASS_LE(count, arity);
      }      
    }
    
    unsigned addedToSorts = 0;
    while(env.sorts->isOfStructuredSort(srt2, Sorts::StructuredSort::FUNCTION)){
      sorts.push(env.sorts->getFuncSort(srt2)->getDomainSort());
      srt2 = env.sorts->getFuncSort(srt2)->getRangeSort();
      addedToSorts++;
    }
    
    OperatorType* type = OperatorType::getFunctionType(arity + addedToSorts, sorts.begin(), srt2);    
    unsigned sklm = env.signature->addSkolemFunction(arity + addedToSorts, 0 ,arity);
    env.statistics->skolemFunctions++;    
    env.signature->getFunction(sklm)->setType(type);
    env.signature->setFunctorSort(sklm, type);

    TermList skolemFunc;  
    if(addedToSorts){
      skolemFunc = FOOLElimAlt::etaExpand(sklm, type, true, args);
      sorts.truncate(sorts.length() - addedToSorts);
    }else{
      skolemFunc = TermList(Term::create(sklm, arity, args.begin()));
    }    
          
    BetaReductionEngine bre = BetaReductionEngine();
    ASS(sigmaTerm.isTerm());
    sigmaTerm = bre.betaReduce(sigmaTerm.term(), skolemFunc); 
      
    expsrt = env.sorts->getFuncSort(expsrt)->getRangeSort();
  }while(!(expsrt == Sorts::SRT_BOOL));   
    
  return sigmaTerm;
}

TermList piRemoval(TermList piTerm, Clause* clause, unsigned expsrt){
  
  CALL("HOLElimination::piRemoval");
  
  ASS(piTerm.isTerm());
  ASS(env.signature->getFunction(piTerm.term()->functor())->lambda());
    
  unsigned maxVar = clause->maxVar();
  do{ 
    maxVar++;
    unsigned srt2 = env.sorts->getFuncSort(expsrt)->getDomainSort();
    TermList newVar;
    if(env.sorts->isOfStructuredSort(srt2, Sorts::StructuredSort::FUNCTION))
    {
      Stack<TermList> dummy;
      OperatorType* type = FOOLElimAlt::toType(srt2);
      unsigned functor = env.signature->addFreshHOVar(type, maxVar);
      env.signature->setFunctorSort(functor, type);      
      newVar = FOOLElimAlt::etaExpand(functor, type, false, dummy);
    } else {
      newVar = TermList(maxVar, false);
    }
    BetaReductionEngine bre = BetaReductionEngine();
    ASS(piTerm.isTerm());
    piTerm = bre.betaReduce(piTerm.term(), newVar); 
   
    expsrt = env.sorts->getFuncSort(expsrt)->getRangeSort();
  }while(!(expsrt == Sorts::SRT_BOOL)); 
  
  return piTerm;
}

/* returns 0 if t1 is a termList representing false, 1
   if it represents true and -1 otherwise.
 */
int isBoolValue(TermList tl){
  CALL("isBoolValue");
  
  if(!tl.isTerm()){ return -1;}
  if(env.signature->isFoolConstantSymbol(true, tl.term()->functor())){ return 1;}
  if(env.signature->isFoolConstantSymbol(false, tl.term()->functor())){ return 0;}
  
  return -1;
}


bool isPISIGMAequality(Literal* lit, TermList &t1, TermList &rhs, bool &applyPIrule, unsigned &srt1)
{
    CALL("isPISIGMAequality");
   
    unique_ptr<ConstantTerm> cnst = isHolConstantEquality(lit);
   
    if(!cnst || (cnst->cnst != SigSym::PI && cnst->cnst != SigSym::SIGMA)){
      return false;
    }
 
    rhs = *lit->nthArgument(1 - cnst->onRight); 
    int rhsValue = isBoolValue(rhs);

    //rhs is not a boolean. Cannot use in simplification rule.
    if(rhsValue < 0){ return false; }
    
    bool isPI = cnst->cnst == SigSym::PI;
    applyPIrule = ((isPI && (rhsValue == lit->polarity())) ||
                  (!isPI && (rhsValue != lit->polarity())));
    rhs = rhsValue == lit->polarity() ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
    t1 = cnst->arg1;
    
    SigSym* sym = env.signature->getFunction(cnst->cnstTerm->functor()); 
    srt1 = sym->fnType()->arg(0); //alpha_1 -> ... alpha_n ->o
    return true; 
}

bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, unsigned &sort)
{
  CALL("isEQUALSApp");
 
  unique_ptr<ConstantTerm> cnst = isHolConstantEquality(lit);
  if(!cnst || (cnst->cnst != SigSym::EQUALS))
  { return false; }
  
  TermList truthValue = *lit->nthArgument(1 - cnst->onRight); 
  int val = isBoolValue(truthValue);
  
  if(val < 0){return false; }
  else {positive = (val == lit->polarity());}

  t1 = cnst->arg1;
  t2 = cnst->arg2;
  SigSym* symbol = env.signature->getFunction(cnst->cnstTerm->functor());
  sort = symbol->fnType()->arg(1);
  return true; 
}

bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
  CALL("appOfORorIMPorAnd");

  unique_ptr<ConstantTerm> cnst = isHolConstantEquality(lit);
  if(!cnst){return false;}

  TermList otherTerm = *lit->nthArgument(1 - cnst->onRight);
  int val = isBoolValue(otherTerm); 
  if(val < 0){ return false;}
   
  if((cnst->cnst == SigSym::AND) && (val == lit->polarity())){ return false;}
  if((cnst->cnst == SigSym::OR)  && (val != lit->polarity())){ return false;}  
  if((cnst->cnst == SigSym::IMP) && (val != lit->polarity())){ return false;}
  
  lhs1 = cnst->arg1;
  lhs2 = cnst->arg2;
  
  TermList troo = TermList(Term::foolTrue());
  TermList fals = TermList(Term::foolFalse());
   
  switch(cnst->cnst){ 
  case SigSym::AND:
    rhs1 = fals; rhs2 = fals; //rule for "and" is t1 = $false \/ t2 = $false ...
    return true;
  case SigSym::OR:
    rhs1 = troo; rhs2 = troo;
    return true;
  case SigSym::IMP:
    rhs1 = fals; rhs2 = troo;
    return true;
  default:
    return false;
  }

  return false;    
}


bool isNOTEquality(Literal* lit, TermList &newEqlhs, TermList &newEqrhs, bool &polarity)
{
    CALL("isNOTEquality");
    
    unique_ptr<ConstantTerm> cnst = isHolConstantEquality(lit);
    if(!cnst || !(cnst->cnst != SigSym::NOT)){ return false; }  
    
    newEqrhs = *lit->nthArgument(1 - cnst->onRight);
    newEqlhs = cnst->arg1;
  
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

Clause* replaceLit2(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d = NULL, Literal* e = NULL )
{
    CALL("replaceLit");

    int length = c->length();
    if(d){ length++;}
    if(e){ length++;}
    
    Clause* res = new(length) Clause(length,
                                     c->inputType(),
                                     inf);

    unsigned i = 0;
    while ((*c)[i] != a) { i++; }
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;
    if(d){(*res)[c->length()] = d;} 
    if(e){(*res)[length - 1] = e;}//adding new literals at differrent places...
    //should this be length AYB?
    
    return res;
}

Clause* ORIMPANDRemovalISE::simplify(Clause* c)
  {
    CALL("ORIMPRemovalISE::simplify");   
    
    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      TermList lhs1, rhs1, lhs2, rhs2;
      Literal *lit = (*c)[i];
      if (appOfORorIMPorAND(lit, lhs1, rhs1, lhs2, rhs2)) {
        Literal* newLit1 = Literal::createEquality(true, lhs1, rhs1, Sorts::SRT_BOOL);
        Literal* newLit2 = Literal::createEquality(true, lhs2, rhs2, Sorts::SRT_BOOL);
        Clause* res = replaceLit2(c, lit, newLit1, new Inference1(Inference::BINARY_CONN_ELIMINATION, c), newLit2);
        res->setAge(c->age());
        env.statistics->holORIMPANDsimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  }
 
Clause* ORIMPANDRemovalISE2::simplify(Clause* c)
  {
    CALL("ORIMPRemovalISE2::simplify");   
    
    TermList subterm;
    TermList newTerm;
    unsigned literalPosition = 0;
    unsigned premLength = c->length();
    Inference* inference = new Inference1(Inference::BINARY_CONN_SHORT_CIRUCIT_EVAL, c);
    
    while(literalPosition < premLength){
      Literal *literal = (*c)[literalPosition];
    
      NonVariableIterator nvi(literal);
      while (nvi.hasNext()) {
        subterm = nvi.next();

        unique_ptr<ConstantTerm> cnst = isHolConstantTerm(subterm);
        if(cnst){
         int val = isBoolValue(cnst->arg1);
         int val2 = isBoolValue(cnst->arg2);
         switch(cnst->cnst){
          case SigSym::AND:
            if(val == 0 || val2 == 0){
              newTerm = TermList(Term::foolFalse());
              goto substitution; 
            }
            break;
          case SigSym::OR:
            if(val == 1 || val2 == 1){ 
              newTerm = TermList(Term::foolTrue());
              goto substitution; 
            }
            break;
          case SigSym::IMP:
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
    
    unsigned conclusionLength = c->length();
 
    Clause* conclusion = new(conclusionLength) Clause(conclusionLength, c->inputType(), inference);
    conclusion->setAge(c->age());
  
    // Copy the literals from the premise except for the one at `literalPosition`,
    for (unsigned i = 0; i < conclusionLength; i++) {
      (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*c)[i], subterm, newTerm) : (*c)[i];
    }
    env.statistics->holORIMPANDshortCircuitEval++;
    return conclusion;
    
  }
 
Clause* NOTRemovalISE::simplify(Clause* c)
  {
    CALL("NOTRemovalISE::simplify");
  
    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      TermList lhs, rhs;
      bool polarity;
      Literal *lit = (*c)[i];
      if (isNOTEquality(lit, lhs, rhs, polarity)) {
        Literal *newLit;
        newLit = Literal::createEquality(polarity, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::HOL_NOT_ELIMINATION, c));//Change inference AYB
        res->setAge(c->age());
        env.statistics->holNOTsimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  } 

Clause* EQUALSRemovalISE::simplify(Clause* c)
  {
    CALL("EQUALSRemovalISE::simplify");
  
    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      TermList lhs, rhs;
      bool polarity;
      unsigned sort;
      Literal *lit = (*c)[i];
      if (isEQUALSApp(lit, lhs, rhs, polarity, sort)) {
        Literal *newLit = Literal::createEquality(polarity, lhs, rhs, sort);//Check this in particular polarity, AYB
        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::HOL_EQUALITY_ELIMINATION, c));//Change inference AYB
        res->setAge(c->age());
        env.statistics->holEQAULSsimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  }   
 
Clause* PISIGMARemovalISE::simplify(Clause* c)
  {
    CALL("PISIGMARemovalISE::simplify");

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      unsigned expsrt;  
      TermList t1, lhs, rhs; 
      bool applyPIrule;
      Literal *lit = (*c)[i];
      if (isPISIGMAequality(lit, t1, rhs, applyPIrule, expsrt)) {
        Literal *newLit;
        //cout << "The original literal was: " + lit->toString() << endl; 
        if(applyPIrule){
          lhs = piRemoval(t1, c, expsrt);                  
        }else{
          lhs = sigmaRemoval(t1, expsrt);
        } 
        
        newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL); 
        
        //cout << "The new literal is: " + newLit->toString() << endl;
        
        Clause* res;
        if(applyPIrule){
           res = replaceLit2(c, lit, newLit, new Inference1(Inference::VPI_ELIMINATION, c));//Change inference AYB
        }else{
           res = replaceLit2(c, lit, newLit, new Inference1(Inference::VSIGMA_ELIMINATION, c));//Change inference AYB
        }           
        res->setAge(c->age());

        env.statistics->holPISIGMAsimplifications++;
        return res;
      }
    }
  
    return c;
  } 

  
  /*
   * Given a clause app(app(binConn, t1), t2) = boolval \/ A, this iterator
   * returns the clauses:
   * (1)  t1 = [~]boolval \/ [t2 = [~]boolval] \/ A 
   * (2)  t2 = [~]boolval \/ [t1 = [~]boolval] \/ A 
   * where [] defines an optional literal/connective that is included depending on the conn
   */
   
  struct ORIMPANDIFFXORRemovalGIE::SubtermIterator
  {
    SubtermIterator(Clause *clause, Literal *lit)
      : _count(0),
        _lit(lit),
        _clause(clause),
        _pol(lit->polarity())
    {
 
      CALL("ORIMPANDIFFXORRemovalGIE::SubtermIterator");
    
    
      unique_ptr<ConstantTerm> cnst = isHolConstantEquality(lit);
      if (cnst) {     

        TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);

        int val = isBoolValue(otherTermt);
        _rhsIsTrue = (val > -1) && ((unsigned)val != _pol);
        _rhsIsFalse = (val > -1) && ((unsigned)val == _pol);
        _rhsIsTerm = val < 0;
        _constant = cnst->cnst; 
        _terms.push(cnst->arg1);
        
        if(cnst->cnst != SigSym::PI && cnst->cnst != SigSym::SIGMA && cnst->cnst != SigSym::NOT){
          _terms.push(cnst->arg2);
        }  
        if(cnst->cnst == SigSym::EQUALS){
          SigSym* sym = env.signature->getFunction(cnst->cnstTerm->functor());
          _termsSort = sym->fnType()->arg(0); //only relevant for equality. All other sorts are bool.
        }
        if(cnst->cnst == SigSym::PI || cnst->cnst == SigSym::SIGMA){
          SigSym* sym = env.signature->getFunction(cnst->cnstTerm->functor());
          _expsort = sym->fnType()->arg(0); 
        }
        if(_rhsIsTerm){_terms.push(otherTermt);}
        
        switch(_constant){
          case SigSym::OR:
          case SigSym::IMP:
           if(_rhsIsTrue){ _count = 4; } //Iterator returns nothing
           break;
          case SigSym::AND:
           if(_rhsIsFalse){ _count = 4; } //Iterator returns nothing
           break;         
          case SigSym::PI:
          case SigSym::SIGMA:
          case SigSym::EQUALS:
           if(!_rhsIsTerm){ _count = 4; } //Iterator returns nothing
           break;
          case SigSym::NOT:
           _count = 4;
          default:
           break;
        }

      }else{
        _count = 4; //Iterator returns nothing (Must be a better way of doing this!)
      }              
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {  
       switch(_constant){
         case SigSym::AND:
         case SigSym::OR:
         case SigSym::IMP:
           if(_rhsIsTerm){ return _count < 3; }
           break;
         case SigSym::XOR:
         case SigSym::IFF:
           if(_rhsIsTerm){ return _count < 4; }
           break;
         default:
           break;
       }
       return _count < 2;            
    }
    OWN_ELEMENT_TYPE next()
    {
      CALL("ORIMPANDIFFXORRemovalGIE::SubtermIterator::next()");

      TermList boolValues[] = {TermList(Term::foolTrue()), TermList(Term::foolFalse())};
    
      Clause *res;
      Inference *inf;
      switch(_constant){
        case SigSym::EQUALS:
          inf = new Inference1(Inference::HOL_EQUALITY_ELIMINATION, _clause); 
          break;
        case SigSym::PI:
          inf = new Inference1(Inference::VPI_ELIMINATION, _clause); 
          break;     
        case SigSym::SIGMA:
          inf = new Inference1(Inference::VSIGMA_ELIMINATION, _clause); 
          break;       
        default:
          inf =  new Inference1(Inference::BINARY_CONN_ELIMINATION, _clause);
      }
      Literal* l1 = NULL;
      Literal* l2 = NULL;
      Literal* l3 = NULL;      
    
      switch(_constant){
        case SigSym::OR:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[1], Sorts::SRT_BOOL);
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL; 
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[0], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);
          }       
          break;
        case SigSym::AND:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[0], Sorts::SRT_BOOL); 
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL) : NULL; 
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[1], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL);
          }       
          break;        
        case SigSym::IMP:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[_count], Sorts::SRT_BOOL);  
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL;
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);           
          }
          break;
        case SigSym::IFF:
          if(_rhsIsTrue || (_rhsIsTerm && _count < 2)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Sorts::SRT_BOOL); 
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL; 
            break;          
          }
          if(_rhsIsFalse || (_rhsIsTerm && _count > 1)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[_count], Sorts::SRT_BOOL);             
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL) : NULL;
            break;
          }       
        case SigSym::XOR:
          if(_rhsIsTrue || (_rhsIsTerm && _count < 2)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[_count], Sorts::SRT_BOOL);         
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL) : NULL;
            break;
          }
          if(_rhsIsFalse || (_rhsIsTerm && _count > 1)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Sorts::SRT_BOOL);                
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL; 
            break;  
          }
        case SigSym::EQUALS:
           l1 = Literal::createEquality(_count, _terms[0], _terms[1], _termsSort);
           l2 = Literal::createEquality(true, _terms[2], boolValues[(_count == _pol)], Sorts::SRT_BOOL);
           break;
        case SigSym::PI:
           if(_count < 1){
             l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[0], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Sorts::SRT_BOOL);
           }else{
             l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[1], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Sorts::SRT_BOOL);          
           }
           break;
        case SigSym::SIGMA:
           if(_count < 1){
             l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[0], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Sorts::SRT_BOOL);
           }else{
             l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[1], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Sorts::SRT_BOOL);
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
      
      /*if(_constant == SigSym::PI || _constant == SigSym::SIGMA){
        cout << "The original clause was: " + _clause->toString() << endl;
        cout << "The new clause is: " + res->toString() << endl;
      }*/
      res->setAge(_clause->age()+1);
      
      env.statistics->holBINARYCONNgeneratingrules++;
      return res;
    }
  private:
    unsigned _expsort; //used for PI and SIGMA only.
    unsigned _count;
    Literal* _lit;
    Clause* _clause;
    unsigned _pol;
    bool _rhsIsTerm;
    bool _rhsIsTrue;
    bool _rhsIsFalse;
    unsigned _termsSort;
    Stack<TermList> _terms;
    SigSym::HOLConstant _constant;
  };

  struct ORIMPANDIFFXORRemovalGIE::SubtermEqualityFn
  {
    SubtermEqualityFn(Clause* premise)
      : _premise(premise) {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("ORIMPANDIFFXORRemovalGIE::SubtermEqualityFn::operator()");

      return pvi(SubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator ORIMPANDIFFXORRemovalGIE::generateClauses(Clause* c)
  {
    CALL("ORIMPANDIFFXORRemovalGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, SubtermEqualityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }  
  
}
