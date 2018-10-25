
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
#include "Kernel/HOSortHelper.hpp"

#include "Shell/LambdaElimination.hpp"
#include "Shell/Statistics.hpp"

#include "HOLElimination.hpp"
#include <memory>

namespace Inferences {

typedef LambdaElimination LE;
typedef HOSortHelper HSH;

ct_ptr isHolConstantApp(TermList tl, unsigned unaryBinaryOrTenary)
{
  CALL("isHolConstantApp(TermList tl)");
    
  ASS(unaryBinaryOrTenary > 0 && unaryBinaryOrTenary < 4);
  
  if(tl.isVar()){
    return 0;
  }

  ct_ptr cnst (new ConstantTerm());

  unsigned argnum=0;
  SS* sym = env.signature->getFunction(tl.term()->functor());
  
  while(sym->hOLAPP()){
    argnum++;

    if(argnum > unaryBinaryOrTenary){ return 0; }

    cnst->args.push(*(tl.term()->nthArgument(1)));
    cnst->sorts.push(SortHelper::getArgSort(tl.term(), 1));

    tl = *(tl.term()->nthArgument(0));
    
    if(tl.isVar()){ return 0; }
    
    sym = env.signature->getFunction(tl.term()->functor());
  }

  if((argnum != unaryBinaryOrTenary)){
    return 0;
  }
  
  if(sym->getConst() == SS::NULL_CONSTANT){
    return 0;
  }

  ASS(cnst->args.size() == unaryBinaryOrTenary);
  cnst->constant = tl.term();
  cnst->cnst = sym->getConst();
  return std::move(cnst);
}


ct_ptr isHolConstantApp(Literal* lit, unsigned unaryBinaryOrTenary)
{
  CALL("isHolConstantApp(Literal* lit)");
  
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

Inference::Rule constToInfRule(SS::HOLConstant cnst){
  CALL("constToInfRule");

  switch(cnst){
    case SS::I_COMB:
      return Inference::I_COMBINATOR_ELIMINATION;
    case SS::K_COMB:
      return Inference::K_COMBINATOR_ELIMINATION;
    case SS::B_COMB:
      return Inference::B_COMBINATOR_ELIMINATION;
    case SS::C_COMB:
      return Inference::C_COMBINATOR_ELIMINATION;
    case SS::S_COMB:  
      return Inference::S_COMBINATOR_ELIMINATION;  
    case SS::PI:
      return Inference::VPI_ELIMINATION;
    case SS::SIGMA:
      return Inference::VSIGMA_ELIMINATION;
    case SS::EQUALS:
      return Inference::HOL_EQUALITY_ELIMINATION;
    case SS::NOT:
      return Inference::HOL_NOT_ELIMINATION;
    default:
      return Inference::BINARY_CONN_ELIMINATION;   
  }

}

TermList sigmaRemoval(TermList sigmaTerm, unsigned expsrt){

  //cout << "INTO sigmaRemoval " + sigmaTerm.toString() << endl;

  Stack<unsigned> sorts;
  Formula::VarList* vars = sigmaTerm.freeVariables();
  Formula::VarList::Iterator fvi(vars);
  DHMap<unsigned,unsigned> _varSorts;
  SortHelper::collectVariableSorts(sigmaTerm.term(), _varSorts);
  while (fvi.hasNext()) {
    unsigned var = (unsigned)fvi.next();
    sorts.push(_varSorts.get(var));
  }
      
  do{ 
    unsigned domain = HSH::domain(expsrt);
    
    //should be able to move this out of the loop
    Stack<TermList> arguments;
    Formula::VarList::Iterator vit(vars);
    while (vit.hasNext()) {
      unsigned var = (unsigned)vit.next();
      arguments.push(TermList(var, false));
    }

    unsigned skSymSort = HSH::getHigherOrderSort(sorts, domain);
    unsigned symbol = env.signature->addSkolemFunction(0);
    env.signature->getFunction(symbol)->setType(OperatorType::getConstantsType(skSymSort));
    TermList head = TermList(Term::createConstant(symbol));
    TermList skolemFunc = TermList(HSH::createAppifiedTerm(head, skSymSort, sorts, arguments));
  
    unsigned app = LE::introduceAppSymbol(expsrt, domain, HSH::range(expsrt));
    sigmaTerm = TermList(Term::create2(app, sigmaTerm, skolemFunc));
      
    expsrt = HSH::range(expsrt);
  }while(!(expsrt == Sorts::SRT_BOOL));   

  //cout << "OUT OF sigmaRemoval " + sigmaTerm.toString() << endl;

  return sigmaTerm;
}

TermList piRemoval(TermList piTerm, Clause* clause, unsigned expsrt){
  
  unsigned maxVar = clause->maxVar();
  do{ 
    maxVar++;
    TermList newVar = TermList(maxVar, false);
    unsigned srt2 = HSH::domain(expsrt);
    unsigned symbol = LE::introduceAppSymbol(expsrt, srt2, HSH::range(expsrt));  
    piTerm = TermList(Term::create2(symbol, piTerm, newVar));
    expsrt = HSH::range(expsrt);
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
   
    ct_ptr cnst = isHolConstantApp(lit, 1);
    if(!cnst || (cnst->cnst != SS::PI && cnst->cnst != SS::SIGMA)){
      return false;
    }
   
    rhs = *lit->nthArgument(1 - cnst->onRight); 
    int rhsValue = isBoolValue(rhs);

    if(rhsValue < 0){ return false; }
    
    bool isPI = cnst->cnst == SS::PI ? true : false;
  
    bool positive = rhsValue == lit->polarity();
    applyPIrule = (isPI && positive) || (!isPI && !positive);
    rhs = positive ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());

    t1 = cnst->args.pop();  
    srt1 = HSH::domain(SortHelper::getResultSort(cnst->constant));
    return true; 
}

bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, unsigned &sort)
{
    CALL("isEQUALSApp");
   
    ct_ptr cnst = isHolConstantApp(lit, 2);
    if(!cnst || cnst->cnst != SS::EQUALS){return false;}
    
    TermList truthValue = *lit->nthArgument(1 - cnst->onRight); 

    int val = isBoolValue(truthValue);
    if(val < 0){return false; }
    else {positive = (val == lit->polarity());}
  
    t1 = cnst->args.pop();
    t2 = cnst->args.pop();
    sort = HSH::domain(SortHelper::getResultSort(cnst->constant));
    return true; 
}

bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
  CALL("appOfORorIMPorAnd");

  ct_ptr cnst = isHolConstantApp(lit, 2);
  if(!cnst){return false;}

  TermList otherTerm = *lit->nthArgument(1 - cnst->onRight);
  int val = isBoolValue(otherTerm); 
  if(val < 0){ return false;}
   
  if((cnst->cnst == SS::AND) && ((val + lit->polarity()) % 2 == 0)){ return false;}
  if((cnst->cnst == SS::OR)  && ((val + lit->polarity()) % 2 == 1)){ return false;}  
  if((cnst->cnst == SS::IMP) && ((val + lit->polarity()) % 2 == 1)){ return false;}
  
  lhs1 = cnst->args.pop();
  lhs2 = cnst->args.pop();
  
  TermList troo = TermList(Term::foolTrue());
  TermList fals = TermList(Term::foolFalse());
   
  switch(cnst->cnst){ 
  case SS::AND:
    rhs1 = fals; rhs2 = fals; //rule for "and" is t1 = $false \/ t2 = $false ...
    return true;
  case SS::OR:
    rhs1 = troo; rhs2 = troo;
    return true;
  case SS::IMP:
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
    
    ct_ptr cnst = isHolConstantApp(lit, 1);
    if(!cnst || cnst->cnst != SS::NOT){return false;}  
    
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

Clause* replaceLit2(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d = NULL, Literal* e = NULL )
{
    CALL("replaceLit");

    int length = c->length();
    if(d){ length++;}
    if(e){ length++;}
    
    Clause* res = new(length) Clause(length, c->inputType(), inf);

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

      ct_ptr cnst = isHolConstantApp(subterm, 2);
      if(cnst){
       int val = isBoolValue(cnst->args[1]);
       int val2 = isBoolValue(cnst->args[0]);
       switch(cnst->cnst){
        case SS::AND:
          if(val == 0 || val2 == 0){
            newTerm = TermList(Term::foolFalse());
            goto substitution; 
          }
          break;
        case SS::OR:
          if(val == 1 || val2 == 1){ 
            newTerm = TermList(Term::foolTrue());
            goto substitution; 
          }
          break;
        case SS::IMP:
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
      //cout << "Into equality removal " + c->toString() << endl;  
      //cout << "Out of equality removal " + res->toString() << endl;
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
      //cout << "Into PISIGMARemovalISE removal " + c->toString() << endl;  
      //cout << "Out of PISIGMARemovalISE removal " + res->toString() << endl;
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
 
      //DHMap<unsigned,unsigned> _varSorts;
      //SortHelper::collectVariableSorts(subterm.term(), _varSorts);

      ct_ptr cnst = isHolConstantApp(subterm, 1);
      if(cnst && cnst->cnst == SS::I_COMB) {
        inference = new Inference1(constToInfRule(cnst->cnst), premise); 
        combinatorTerm = subterm;
        newTerm        = cnst->args.pop();
        goto substitution;
      }

      cnst = isHolConstantApp(subterm, 2);
      if(cnst && cnst->cnst == SS::K_COMB) {
        inference = new Inference1(constToInfRule(cnst->cnst), premise); 
        combinatorTerm = subterm;
        newTerm        = cnst->args.pop();
        goto substitution;
      }
  
      cnst = isHolConstantApp(subterm, 3);
      if (cnst && (cnst->cnst == SS::B_COMB ||
                   cnst->cnst == SS::C_COMB ||
                   cnst->cnst == SS::S_COMB )){

        TermList t1 = cnst->args.pop();
        TermList t2 = cnst->args.pop();
        TermList t3 = cnst->args.pop();
        unsigned t1sort  = cnst->sorts.pop();
        unsigned t2sort  = cnst->sorts.pop();
        unsigned t3sort  = cnst->sorts.pop();
    
        TermList tl1;
        TermList tl2; 
        if(cnst->cnst != SS::C_COMB){
          unsigned appt2tot3 = LE::introduceAppSymbol(t2sort, t3sort, HSH::range(t2sort));
          tl2 = TermList(Term::create2(appt2tot3, t2, t3));
        } else {
          tl2 = t2;
        }

       if(cnst->cnst != SS::B_COMB){
          unsigned appt1tot3 = LE::introduceAppSymbol(t1sort, t3sort, HSH::range(t1sort));
          tl1 = TermList(Term::create2(appt1tot3, t1, t3));
        } else {
          tl1 = t1;
        }
        unsigned s1 = tl1.isVar() ? t1sort : SortHelper::getResultSort(tl1.term());
        unsigned s2 = tl2.isVar() ? t2sort : SortHelper::getResultSort(tl2.term());

        ASS(HSH::domain(s1) == s2);
        
        unsigned app = LE::introduceAppSymbol(s1, s2, HSH::range(s1));
        newTerm = TermList(Term::create2(app, tl1, tl2));
        combinatorTerm = subterm; 
        inference = new Inference1(constToInfRule(cnst->cnst), premise); 
        goto substitution;
      }

    }
    literalPosition++;
  }

// If we reached this point, it means that no fully applied combinator
// was found, so we know that no simplification can be carried out. 

return premise;

substitution:

// Found a fully applied combinator term!
unsigned conclusionLength = premise->length();

Clause* conclusion = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference);
conclusion->setAge(premise->age());

//cout << "replacing " + combinatorTerm.toString() + " with " + newTerm.toString() + " in premise " + premise->toString() << endl;

// Copy the literals from the premise except for the one at `literalPosition`,
for (unsigned i = 0; i < conclusionLength; i++) {
  (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], combinatorTerm, newTerm) : (*premise)[i];
}

//cout << "The premise is " + premise->toString() << endl;
//cout << "The result is " + conclusion->toString() << endl;

return conclusion;
    
}

  
/*
 * Given a clause app(app(binConn, t1), t2) = boolval \/ A, this iterator
 * returns the clauses:
 * (1)  t1 = [~]boolval \/ [t2 = [~]boolval] \/ A 
 * (2)  t2 = [~]boolval \/ [t1 = [~]boolval] \/ A 
 * where [] defines an optional literal/connective that is included depending on the conn
 */
 
struct ORIMPANDIFFXORRemovalGIE::ProxyEliminationIterator
{
  ProxyEliminationIterator(Clause *clause, Literal *lit)
    : _count(0),
      _lit(lit),
      _clause(clause),
      _pol(lit->polarity())
  {

    CALL("ORIMPANDIFFXORRemovalGIE::ProxyEliminationIterator");
  
    ct_ptr cnst = isHolConstantApp(lit, 2);
    if (cnst) {     

      TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
      
      int val = isBoolValue(otherTermt);
      _rhsIsTrue = (val > -1) && ((unsigned)val == _pol);
      _rhsIsFalse = (val > -1) && ((unsigned)val != _pol);
      _rhsIsTerm = val < 0;
      _terms.push(cnst->args.pop());
      _terms.push(cnst->args.pop());
      _termsSort = cnst->sorts.pop(); //only relevant for equality. All other sorts are bool.
      if(_rhsIsTerm){_terms.push(otherTermt);}
        
      _constant = cnst->cnst; 
      
      switch(_constant){
        case SS::OR:
        case SS::IMP:
         if(_rhsIsTrue){ _count = 4; } //Iterator returns nothing
         break;
        case SS::AND:
         if(_rhsIsFalse){ _count = 4; } //Iterator returns nothing
         break;
        case SS::EQUALS:
         if(!_rhsIsTerm){ _count = 4; } //Iterator returns nothing
         break;
        case SS::B_COMB:
        case SS::C_COMB:
        case SS::I_COMB:
        case SS::K_COMB:
        case SS::S_COMB:
          _count = 4;
          break;
        default:
          break;
      }
    } else {
      cnst = isHolConstantApp(lit, 1);
      if(cnst && (cnst->cnst == SS::PI || cnst->cnst == SS::SIGMA)){
        TermList otherTermt = *lit->nthArgument(1 - cnst->onRight);
        if (isBoolValue(otherTermt) > -1){
          _count = 4;
        } else {
          _constant = cnst->cnst; 
          _terms.push(cnst->args.pop());
          _terms.push(otherTermt);
          SS* sym = env.signature->getFunction(cnst->constant->functor());
          _expsort = sym->fnType()->result();
          _expsort = env.sorts->getFuncSort(_expsort)->getDomainSort();
        }      
      }else{
        _count = 4; //Iterator returns nothing (Must be a better way of doing this!)
      }
    }
  }

  DECL_ELEMENT_TYPE(Clause *);

  bool hasNext() {  
     switch(_constant){
       case SS::AND:
       case SS::OR:
       case SS::IMP:
         if(_rhsIsTerm){ return _count < 3; }
         break;
       case SS::XOR:
       case SS::IFF:
         if(_rhsIsTerm){ return _count < 4; }
         break;
       default:
         break;
     }
     return _count < 2;            
  }
  OWN_ELEMENT_TYPE next()
  {
    CALL("ORIMPANDIFFXORRemovalGIE::proxyEliminationIterator::next()");

    TermList boolValues[] = {TermList(Term::foolTrue()), TermList(Term::foolFalse())};
  
    Clause *res;
    Inference *inf = new Inference1(constToInfRule(_constant), _clause);

    Literal* l1 = NULL;
    Literal* l2 = NULL;
    Literal* l3 = NULL;      
  
    switch(_constant){
      case SS::OR:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[1], Sorts::SRT_BOOL);
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL; 
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[0], Sorts::SRT_BOOL);
          l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
          l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);
        }       
        break;
      case SS::AND:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[0], Sorts::SRT_BOOL); 
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL) : NULL; 
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
          l2 = Literal::createEquality(true, _terms[1], boolValues[1], Sorts::SRT_BOOL);
          l3 = Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL);
        }       
        break;        
      case SS::IMP:
        if(_count < 2){
          l1 = Literal::createEquality(true, _terms[_count], boolValues[_count], Sorts::SRT_BOOL);  
          l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1 - _pol], Sorts::SRT_BOOL) : NULL;
        }else{
          l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
          l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
          l3 = Literal::createEquality(true, _terms[2], boolValues[_pol], Sorts::SRT_BOOL);           
        }
        break;
      case SS::IFF:
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
      case SS::XOR:
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
      case SS::EQUALS:
         l1 = Literal::createEquality(_count, _terms[0], _terms[1], _termsSort);
         l2 = Literal::createEquality(true, _terms[2], boolValues[(_count == _pol)], Sorts::SRT_BOOL);
         break;
      case SS::PI:
         if(_count < 1){
           l1 = Literal::createEquality(true, piRemoval(_terms[0], _clause, _expsort), boolValues[0], Sorts::SRT_BOOL);
           l2 = Literal::createEquality(true, _terms[1], boolValues[(1 == _pol)], Sorts::SRT_BOOL);
         }else{
           l1 = Literal::createEquality(true, sigmaRemoval(_terms[0], _expsort), boolValues[1], Sorts::SRT_BOOL);
           l2 = Literal::createEquality(true, _terms[1], boolValues[(0 == _pol)], Sorts::SRT_BOOL);          
         }
         break;
      case SS::SIGMA:
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
    
    
    //if(_constant == SS::AND || _constant == SS::OR || _constant == SS::IMP){
      //cout << "The original clause is: " + _clause->toString() << endl;
      //cout << "The new clause is: " + res->toString() << endl;
    //}

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
  SS::HOLConstant _constant;
};

struct ORIMPANDIFFXORRemovalGIE::ProxyEliminationFn
{
  ProxyEliminationFn(Clause* premise)
    : _premise(premise) {}
  DECL_RETURN_TYPE(VirtualIterator<Clause*>);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    CALL("ORIMPANDIFFXORRemovalGIE::SubtermEqualityFn::operator()");

    return pvi(ProxyEliminationIterator(_premise, lit));
  }
private:
  Clause* _premise;
};

ClauseIterator ORIMPANDIFFXORRemovalGIE::generateClauses(Clause* c)
{
  CALL("ORIMPANDIFFXORRemovalGIE::generateClauses");

  auto it1 = c->getSelectedLiteralIterator();
  auto it2 = getMappingIterator(it1, ProxyEliminationFn(c));
  auto it3 = getFlattenedIterator(it2);
  return pvi(it3);
}  
  
}
