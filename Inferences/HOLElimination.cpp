
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

#include "HOLElimination.hpp"
#include <memory>

namespace Inferences {


unsigned introduceAppSymbol(unsigned sort1, unsigned sort2, unsigned resultSort) {
    
  CALL("HOLElimination::introduceAppSymbol");

  ASS(env.sorts->getFuncSort(sort1)->getDomainSort() == sort2);
  ASS(env.sorts->getFuncSort(sort1)->getRangeSort() == resultSort);
  
  Stack<unsigned> sorts;
  sorts.push(sort1); sorts.push(sort2);
  OperatorType* type = OperatorType::getFunctionType(2, sorts.begin(), resultSort);
  unsigned symbol;
  bool added = false;
  
  vstring srt1 = Lib::Int::toString(sort1);
  vstring srt2 = Lib::Int::toString(sort2);
  symbol = env.signature->addFunction("vAPP_" + srt1 + "_" + srt2, 2, added);
  
  if(added){
   env.signature->getFunction(symbol)->setType(type);
   env.signature->getFunction(symbol)->markHOLAPP();
  }
  
  return symbol;
}

unique_ptr<ConstantTerm> isHolConstantApp(Literal* lit, unsigned unaryBinaryOrTenary)
{
  CALL("isHolConstantApp(Literal* lit)");
  
  if(!lit->isEquality()){ return NULL; }
  
  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);  
  
  unique_ptr<ConstantTerm> cnst = isHolConstantApp(lhs, unaryBinaryOrTenary);
  if(cnst){
    cnst->onRight = 0;
    return std::move(cnst);
  }
  
  cnst = isHolConstantApp(rhs, unaryBinaryOrTenary);
  if(cnst){
    cnst->onRight = 1;
    return std::move(cnst);
  }  
  
  return NULL;
  
}

unique_ptr<ConstantTerm> isHolConstantApp(TermList tl, unsigned unaryBinaryOrTenary)
{
  CALL("isHolConstantApp(TermList tl)");
  
  unique_ptr<ConstantTerm> cnst (new ConstantTerm());
  Signature::Symbol* sym;
  
  ASS(unaryBinaryOrTenary > 0 && unaryBinaryOrTenary < 4);
  
  if(tl.isTerm()){
    Term* term1 = tl.term();
    sym = env.signature->getFunction(term1->functor());
    if(sym->hOLAPP()){
      TermList arg1 = *term1->nthArgument(0);
      TermList arg2 = *term1->nthArgument(1);

      if(!arg1.isTerm()){ return NULL; }
      Term* term2 = arg1.term();
      sym = env.signature->getFunction(term2->functor());
 
      if(unaryBinaryOrTenary == 1){    
        if(sym->getConst() == Signature::Symbol::NULL_CONSTANT){ return NULL; }
        cnst->constant = term2;
        cnst->t1 = arg2;
        cnst->t1Sort = SortHelper::getArgSort(term1, 1);
        cnst->cnst = sym->getConst();
        return std::move(cnst);
      }

      if(sym->hOLAPP()){
        TermList arg1of1 = *term2->nthArgument(0);
        TermList arg2of1 = *term2->nthArgument(1);
        
        if(!arg1of1.isTerm()){ return NULL; }
        Term* term3 = arg1of1.term();
        sym = env.signature->getFunction(term3->functor());
        
          
        if(unaryBinaryOrTenary == 2){    
          if(sym->getConst() == Signature::Symbol::NULL_CONSTANT){ return NULL; }
          cnst->cnst = sym->getConst();
          cnst->constant = term3;
          cnst->t2 = arg2;
          cnst->t2Sort = SortHelper::getArgSort(term1, 1);
          cnst->t1 = arg2of1;
          cnst->t1Sort = SortHelper::getArgSort(term2, 1);
          return std::move(cnst);
        }
      
        if(sym->hOLAPP()){
          TermList arg1of1of1 = *term3->nthArgument(0);
          TermList arg2of1of1 = *term3->nthArgument(1);
      
          if(!arg1of1of1.isTerm()){ return NULL; }
          Term* term4 = arg1of1of1.term();
          sym = env.signature->getFunction(term4->functor());
          if(sym->getConst() == Signature::Symbol::NULL_CONSTANT){ return NULL; }
          
          cnst->t3 = arg2;
          cnst->t3Sort = SortHelper::getArgSort(term1, 1);
          cnst->t2 = arg2of1;
          cnst->t2Sort = SortHelper::getArgSort(term2, 1);
          cnst->t1 = arg2of1of1;
          cnst->t1Sort = SortHelper::getArgSort(term3, 1);
          cnst->constant = term4;
          cnst->cnst = sym->getConst();
          return std::move(cnst);
        }
      }
    }
  }
  return NULL;
}

TermList sigmaRemoval(TermList sigmaTerm, unsigned expsrt){
  Stack<unsigned> sorts;
  Formula::VarList* vars = sigmaTerm.freeVariables();
  Formula::VarList::Iterator fvi(vars);
  DHMap<unsigned,unsigned> _varSorts;
  SortHelper::collectVariableSorts(sigmaTerm.term(), _varSorts);
  while (fvi.hasNext()) {
    unsigned var = (unsigned)fvi.next();
    sorts.push(_varSorts.get(var));
  }         
  unsigned arity = (unsigned)sorts.size();
      
  do{ 
    unsigned srt2 = env.sorts->getFuncSort(expsrt)->getDomainSort();
    OperatorType* type = OperatorType::getFunctionType(arity, sorts.begin(), srt2);

    unsigned symbol = env.signature->addSkolemFunction(arity);    
    env.signature->getFunction(symbol)->setType(type);
          
    Stack<TermList> arguments;
    Formula::VarList::Iterator vit(vars);
    while (vit.hasNext()) {
      unsigned var = (unsigned)vit.next();
      arguments.push(TermList(var, false));
    }
    TermList skolemFunc = TermList(Term::create(symbol, arity, arguments.begin()));
    symbol = introduceAppSymbol(expsrt, srt2, env.sorts->getFuncSort(expsrt)->getRangeSort());
    sigmaTerm = TermList(Term::create2(symbol, sigmaTerm, skolemFunc));
      
    expsrt = env.sorts->getFuncSort(expsrt)->getRangeSort();
  }while(!(expsrt == Sorts::SRT_BOOL));   
  
  return sigmaTerm;
}

TermList piRemoval(TermList piTerm, Clause* clause, unsigned expsrt){
  
  unsigned maxVar = 0;
  DHSet<unsigned> vars;
  clause->collectVars(vars);
  DHSet<unsigned>::Iterator vit(vars);
  while(vit.hasNext()){
    unsigned var = vit.next();
    if (var > maxVar) { maxVar = var;}
  }
  do{ 
    maxVar++;
    TermList newVar = TermList(maxVar, false);
    unsigned srt2 = env.sorts->getFuncSort(expsrt)->getDomainSort();
    unsigned symbol = introduceAppSymbol(expsrt, srt2, env.sorts->getFuncSort(expsrt)->getRangeSort());  
    piTerm = TermList(Term::create2(symbol, piTerm, newVar));
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


bool isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &applyPIrule, unsigned &srt1)
{
    CALL("isPISIGMAapp");
   
    unique_ptr<ConstantTerm> cnst = isHolConstantApp(lit, 1);
    if(!cnst){return false;}
   
    if(cnst->cnst != Signature::Symbol::PI && cnst->cnst != Signature::Symbol::SIGMA){
      return false;
    }
 
    rhs = *lit->nthArgument(1 - cnst->onRight); 
    int rhsValue = isBoolValue(rhs);

    if(rhsValue < 0){ return false; }
    
    Signature::Symbol* sym = env.signature->getFunction(cnst->constant->functor());
    bool isPI = cnst->cnst == Signature::Symbol::PI ? true : false;
  
    if((isPI && (rhsValue == lit->polarity()))|| (!isPI && (rhsValue == (1 - lit->polarity()))))
    {
      applyPIrule = true;
    }else{
      applyPIrule = false;
    }

    rhs = rhsValue == lit->polarity() ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());

    t1 = cnst->t1;  
    srt1 = sym->fnType()->result();
    srt1 = env.sorts->getFuncSort(srt1)->getDomainSort();
    return true; 
}

bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, unsigned &sort)
{
    CALL("isEQUALSApp");
   
    unique_ptr<ConstantTerm> cnst = isHolConstantApp(lit, 2);
    if(!cnst){return false;}
    if(!(cnst->cnst == Signature::Symbol::EQUALS)){ return false; }
    
    TermList truthValue = *lit->nthArgument(1 - cnst->onRight); 

    int val = isBoolValue(truthValue);
    if(val < 0){return false; }
    else {positive = (val == lit->polarity());}
  
    t1 = cnst->t1;
    t2 = cnst->t2;
    Signature::Symbol* symbol = env.signature->getFunction(cnst->constant->functor());
    sort = symbol->fnType()->result();
    sort = env.sorts->getFuncSort(sort)->getDomainSort();
    return true; 
}

bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
  CALL("appOfORorIMPorAnd");

  unique_ptr<ConstantTerm> cnst = isHolConstantApp(lit, 2);
  if(!cnst){return false;}

  TermList otherTerm = *lit->nthArgument(1 - cnst->onRight);
  int val = isBoolValue(otherTerm); 
  if(val < 0){ return false;}
   
  if((cnst->cnst == Signature::Symbol::AND) && ((val + lit->polarity()) % 2 == 0)){ return false;}
  if((cnst->cnst == Signature::Symbol::OR)  && ((val + lit->polarity()) % 2 == 1)){ return false;}  
  if((cnst->cnst == Signature::Symbol::IMP) && ((val + lit->polarity()) % 2 == 1)){ return false;}
  
  lhs1 = cnst->t1;
  lhs2 = cnst->t2;
  
  TermList troo = TermList(Term::foolTrue());
  TermList fals = TermList(Term::foolFalse());
   
  switch(cnst->cnst){ 
  case Signature::Symbol::AND:
    rhs1 = fals; rhs2 = fals; //rule for "and" is t1 = $false \/ t2 = $false ...
    return true;
  case Signature::Symbol::OR:
    rhs1 = troo; rhs2 = troo;
    return true;
  case Signature::Symbol::IMP:
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
    
    unique_ptr<ConstantTerm> cnst = isHolConstantApp(lit, 1);
    if(!cnst){return false;}
    if(!(cnst->cnst == Signature::Symbol::NOT)){ return false; }    
    
    newEqrhs = *lit->nthArgument(1 - cnst->onRight);
    newEqlhs = cnst->t1;
  
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

        unique_ptr<ConstantTerm> cnst = isHolConstantApp(subterm, 2);
        if(cnst){
         int val = isBoolValue(cnst->t1);
         int val2 = isBoolValue(cnst->t2);
         switch(cnst->cnst){
          case Signature::Symbol::AND:
            if(val == 0 || val2 == 0){
              newTerm = TermList(Term::foolFalse());
              goto substitution; 
            }
            break;
          case Signature::Symbol::OR:
            if(val == 1 || val2 == 1){ 
              newTerm = TermList(Term::foolTrue());
              goto substitution; 
            }
            break;
          case Signature::Symbol::IMP:
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
      if (isPISIGMAapp(lit, t1, rhs, applyPIrule, expsrt)) {
        Literal *newLit;
   
        if(applyPIrule){
          lhs = piRemoval(t1, c, expsrt);                  
        }else{
          lhs = sigmaRemoval(t1, expsrt);
        } 

        newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL); 

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
  
    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  } 

  Clause* CombinatorEliminationISE::simplify(Clause* premise)
  {
    CALL("CombinatorEliminationISE::simplify");
   
    TermList combinatorTerm;
    TermList newTerm;
    unsigned literalPosition = 0;
    unsigned premLength = premise->length();
    Inference* inference;
    
    while(literalPosition < premLength){
      Literal *literal = (*premise)[literalPosition];
    
      NonVariableIterator nvi(literal);
      while (nvi.hasNext()) {

        TermList subterm = nvi.next();
        DHMap<unsigned,unsigned> _varSorts;
        SortHelper::collectVariableSorts(subterm.term(), _varSorts);
    
        unique_ptr<ConstantTerm> cnst = isHolConstantApp(subterm, 1);
        if(cnst && cnst->cnst == Signature::Symbol::I_COMB) {
          inference = new Inference1(Inference::I_COMBINATOR_ELIMINATION, premise); 
          combinatorTerm = subterm;
          newTerm        = cnst->t1;
          goto substitution;
        }
    
        cnst = isHolConstantApp(subterm, 2);
        if (cnst && cnst->cnst == Signature::Symbol::K_COMB) {
          inference = new Inference1(Inference::K_COMBINATOR_ELIMINATION, premise); 
          combinatorTerm = subterm;   
          newTerm        = cnst->t1;
          goto substitution;
        }
    
        cnst = isHolConstantApp(subterm, 3);
        if (cnst && (cnst->cnst == Signature::Symbol::B_COMB ||
                     cnst->cnst == Signature::Symbol::C_COMB ||
                     cnst->cnst == Signature::Symbol::S_COMB )){
                       
          TermList t1 = cnst->t1;
          TermList t2 = cnst->t2;
          TermList t3 = cnst->t3;
          unsigned t1sort  = SortHelper::getResultSort(t1, _varSorts);
          unsigned t2sort  = SortHelper::getResultSort(t2, _varSorts);
          unsigned t3sort  = SortHelper::getResultSort(t3, _varSorts);
          unsigned ranget1 = env.sorts->getFuncSort(t1sort)->getRangeSort();
      
          switch(cnst->cnst){
            case Signature::Symbol::B_COMB:{
              inference = new Inference1(Inference::B_COMBINATOR_ELIMINATION, premise); 
              unsigned ranget2     = env.sorts->getFuncSort(t2sort)->getRangeSort();
              unsigned appt2tot3   = introduceAppSymbol(t2sort, t3sort, ranget2);
              unsigned appt1       = introduceAppSymbol(t1sort, ranget2, ranget1);
      
              TermList appOft2tot3 = TermList(Term::create2(appt2tot3, t2, t3));
              TermList appOft1     = TermList(Term::create2(appt1, t1, appOft2tot3));

              combinatorTerm = subterm;     
              newTerm        = appOft1;
              goto substitution;
            }
            case Signature::Symbol::C_COMB:{
              inference = new Inference1(Inference::C_COMBINATOR_ELIMINATION, premise); 
              unsigned rangeOfRangeOft1 = env.sorts->getFuncSort(ranget1)->getRangeSort();
              unsigned appt1tot3        = introduceAppSymbol(t1sort, t3sort, ranget1);
              unsigned appt1tot3tot2    = introduceAppSymbol(ranget1, t2sort, rangeOfRangeOft1);
      
              TermList appOft1tot3 = TermList(Term::create2(appt1tot3, t1, t3));
              TermList apptot2     = TermList(Term::create2(appt1tot3tot2, appOft1tot3, t2));

              combinatorTerm = subterm;     
              newTerm        = apptot2;
              goto substitution;
            }
            case Signature::Symbol::S_COMB:{
              inference = new Inference1(Inference::S_COMBINATOR_ELIMINATION, premise); 
              unsigned rangeOfRangeOft1 = env.sorts->getFuncSort(ranget1)->getRangeSort();
              unsigned ranget2          = env.sorts->getFuncSort(t2sort)->getRangeSort();
              unsigned appt1tot3        = introduceAppSymbol(t1sort, t3sort, ranget1);
              unsigned appt2tot3        = introduceAppSymbol(t2sort, t3sort, ranget2);     
              unsigned app              = introduceAppSymbol(ranget1, ranget2, rangeOfRangeOft1);
      
              TermList appOft1tot3 = TermList(Term::create2(appt1tot3, t1, t3));
              TermList appOft2tot3 = TermList(Term::create2(appt2tot3, t2, t3));
              TermList appOf       = TermList(Term::create2(app, appOft1tot3, appOft2tot3));
      
              combinatorTerm = subterm;
              newTerm        = appOf;
              goto substitution;  
            }
            default:
              ASSERTION_VIOLATION;
            }
        }
  
      }
      literalPosition++;
    }

  // If we reached this point, it means that no fully applied combinator
  // was found, so we no simplification can be carried out. 
  return premise;

  substitution:

  // Found a fully applied combinator term!
  unsigned conclusionLength = premise->length();
 
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference);
  conclusion->setAge(premise->age());
  
  // Copy the literals from the premise except for the one at `literalPosition`,
  for (unsigned i = 0; i < conclusionLength; i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], combinatorTerm, newTerm) : (*premise)[i];
  }
  return conclusion;
      
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
    
    
      unique_ptr<ConstantTerm> cnst = isHolConstantApp(lit, 2);
      if (cnst) {     

        TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
        
        int val = isBoolValue(otherTermt);
        _rhsIsTrue = (val > -1) && (val != _pol);
        _rhsIsFalse = (val > -1) && (val == _pol);
        _rhsIsTerm = val < 0;
        _terms.push(cnst->t1);
        _terms.push(cnst->t2);
        _termsSort = cnst->t1Sort; //only relevant for equality. All other sorts are bool.
        if(_rhsIsTerm){_terms.push(otherTermt);}
          
        _constant = cnst->cnst; 
        
        switch(_constant){
          case Signature::Symbol::OR:
          case Signature::Symbol::IMP:
           if(_rhsIsTrue){ _count = 4; } //Iterator returns nothing
           break;
          case Signature::Symbol::AND:
           if(_rhsIsFalse){ _count = 4; } //Iterator returns nothing
           break;
          case Signature::Symbol::EQUALS:
           if(!_rhsIsTerm){ _count = 4; } //Iterator returns nothing
           break;
          case Signature::Symbol::B_COMB:
          case Signature::Symbol::C_COMB:
          case Signature::Symbol::I_COMB:
          case Signature::Symbol::K_COMB:
          case Signature::Symbol::S_COMB:
            _count = 4;
            break;
          default:
            break;
        }
      } else {
        cnst = isHolConstantApp(lit, 1);
        if(cnst){
          TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
          if (isBoolValue(otherTermt) > -1){
            _count = 4;
          }else if(cnst->cnst == Signature::Symbol::PI || cnst->cnst == Signature::Symbol::SIGMA){
            _constant = cnst->cnst; 
            _terms.push(cnst->t1);
            _terms.push(otherTermt);
            Signature::Symbol* sym = env.signature->getFunction(cnst->constant->functor());
            _expsort = sym->fnType()->result();
            _expsort = env.sorts->getFuncSort(_expsort)->getDomainSort();
          }else{
            _count = 4;
          }         
        }else{
          _count = 4; //Iterator returns nothing (Must be a better way of doing this!)
        }
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {  
       switch(_constant){
         case Signature::Symbol::AND:
         case Signature::Symbol::OR:
         case Signature::Symbol::IMP:
           if(_rhsIsTerm){ return _count < 3; }
           break;
         case Signature::Symbol::XOR:
         case Signature::Symbol::IFF:
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
        case Signature::Symbol::EQUALS:
          inf = new Inference1(Inference::HOL_EQUALITY_ELIMINATION, _clause); 
          break;
        case Signature::Symbol::PI:
          inf = new Inference1(Inference::VPI_ELIMINATION, _clause); 
          break;     
        case Signature::Symbol::SIGMA:
          inf = new Inference1(Inference::VSIGMA_ELIMINATION, _clause); 
          break;       
        default:
          inf =  new Inference1(Inference::BINARY_CONN_ELIMINATION, _clause);
      }
      Literal* l1 = NULL;
      Literal* l2 = NULL;
      Literal* l3 = NULL;      
    
      switch(_constant){
        case Signature::Symbol::OR:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[1], Sorts::SRT_BOOL);
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL; 
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[0], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);
          }       
          break;
        case Signature::Symbol::AND:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[0], Sorts::SRT_BOOL); 
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL) : NULL; 
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[1], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL);
          }       
          break;        
        case Signature::Symbol::IMP:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[_count], Sorts::SRT_BOOL);  
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL;
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);           
          }
          break;
        case Signature::Symbol::IFF:
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
        case Signature::Symbol::XOR:
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
        case Signature::Symbol::EQUALS:
           l1 = Literal::createEquality(_count, _terms[0], _terms[1], _termsSort);
           l2 = Literal::createEquality(true, _terms[2], boolValues[(_count == _pol)], Sorts::SRT_BOOL);
           break;
        case Signature::Symbol::PI:
           if(_count < 1){
             l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[0], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Sorts::SRT_BOOL);
           }else{
             l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[1], Sorts::SRT_BOOL);
             l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Sorts::SRT_BOOL);          
           }
           break;
        case Signature::Symbol::SIGMA:
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
      
      /*if(_constant == Signature::Symbol::PI || _constant == Signature::Symbol::SIGMA){
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
    Signature::Symbol::HOLConstant _constant;
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
