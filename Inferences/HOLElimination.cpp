
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


bool isUnaryConstantApp(Literal* lit, int &onRight)
{
    CALL("isUnaryConstantApp");

    if(!lit->isEquality())
        return false;    
    
  onRight = 0;
  
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    
    if(rhs.isTerm()){
        Term* rhst = rhs.term();
        Signature::Symbol* symbol = env.signature->getFunction(rhst->functor());
        if(symbol->hOLAPP()){ //if rhs is of form vAPP(...
            TermList firstArg = *rhst->nthArgument(0);
            if(firstArg.isTerm()){
                rhst = firstArg.term();
                symbol = env.signature->getFunction(rhst->functor());
                if(!(symbol->getConst() == Signature::Symbol::NULL_CONSTANT)){
                   onRight = 1; return true;
                }
            }
        }
    }
    if(lhs.isTerm()){
        Term* lhst = lhs.term();
        Signature::Symbol* symbol = env.signature->getFunction(lhst->functor());
        if(symbol->hOLAPP()){ //if lhs is of form vAPP(...
            TermList firstArg = *lhst->nthArgument(0);
            if(firstArg.isTerm()){
                lhst = firstArg.term();
                symbol = env.signature->getFunction(lhst->functor());
                if(!(symbol->getConst() == Signature::Symbol::NULL_CONSTANT)){
                   return true;
                }
            }
        }
    }
    return false;      
}


bool isBinaryConstantApp(Literal* lit, int &onRight)
{
    CALL("isBinaryConstantApp");
    
    if(!lit->isEquality())
        return false;   
  
    onRight = 0;
  
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);    

    if(rhs.isTerm()){
        Term* rhst = rhs.term();
        Signature::Symbol* symbol = env.signature->getFunction(rhst->functor());
        if(symbol->hOLAPP()){ //if rhs is of form vAPP(...
            TermList firstArg = *rhst->nthArgument(0);
            if(firstArg.isTerm()){
                rhst = firstArg.term();
                symbol = env.signature->getFunction(rhst->functor());
                if(symbol->hOLAPP()){ //if rhs is of form vAPP(vAPP(...
                    firstArg = *rhst->nthArgument(0);
                    if(firstArg.isTerm()){
                        Term* cont = firstArg.term();
                        symbol = env.signature->getFunction(cont->functor());
                        if(!(symbol->getConst() == Signature::Symbol::NULL_CONSTANT)){
                            onRight = 1; return true;
                        }
                    }
                }
            }
        }
    }   
    if(lhs.isTerm()){
        Term* lhst = lhs.term();
        Signature::Symbol* symbol = env.signature->getFunction(lhst->functor());
        if(symbol->hOLAPP()){ //if lhs is of form vAPP(...
            TermList firstArg = *lhst->nthArgument(0);
            if(firstArg.isTerm()){
                lhst = firstArg.term();
                symbol = env.signature->getFunction(lhst->functor());
                if(symbol->hOLAPP()){ //if lhs is of form vAPP(vAPP(...
                    firstArg = *lhst->nthArgument(0);
                    if(firstArg.isTerm()){
                        Term* cont = firstArg.term();
                        symbol = env.signature->getFunction(cont->functor());
                        if(!(symbol->getConst() == Signature::Symbol::NULL_CONSTANT)){
                            return true;
                        }
                    }
                }
            }
        }
    }

    return false;   
}

/* returns 0 if t1 is a termList representing false, 1
   if it represents true and -1 otherwise.
 */
int isBoolValue(TermList tl){
  CALL("isBoolValue");
  
  if(!tl.isTerm()) return -1;
  if(env.signature->isFoolConstantSymbol(true, tl.term()->functor())) return 1;
  if(env.signature->isFoolConstantSymbol(false, tl.term()->functor())) return 0;
  
  return -1;
}


bool isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &rhsIsTrue, bool &rhsIsFalse, bool &isPI,
                  unsigned &srt1)
{
    CALL("isPISIGMAapp");

    int onRight;
    if(!isUnaryConstantApp(lit, onRight))
       return false;
   
    TermList appTerm = *lit->nthArgument(onRight); 
    rhs = *lit->nthArgument(1 - onRight);    
  
    int rhsValue = isBoolValue(rhs);
    if (rhsValue > -1){
      rhsIsTrue  = (rhsValue == lit->polarity()); 
      rhsIsFalse = !rhsIsTrue;
      rhs = rhsIsTrue ? TermList(Term::foolTrue()) : TermList(Term::foolFalse());
    }else{
      rhsIsTrue = false;
      rhsIsFalse = false;
    }

    t1 = *appTerm.term()->nthArgument(1);  
   
    Term* constant = appTerm.term()->nthArgument(0)->term();
    Signature::Symbol* sym = env.signature->getFunction(constant->functor());
    Signature::Symbol::HOLConstant cont = sym->getConst();
    if(cont == Signature::Symbol::PI || cont== Signature::Symbol::SIGMA){      
        isPI = cont == Signature::Symbol::PI ? true : false;
        srt1 = sym->fnType()->result();
        srt1 = env.sorts->getFuncSort(srt1)->getDomainSort();
        return true;
    }               
    
    return false;   
    
}

bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive)
{
    CALL("isEQUALSApp");

    int onRight;
    if(!(isBinaryConstantApp(lit, onRight)))
        return false;
     
    Term* appTerm = lit->nthArgument(onRight)->term();
    TermList truthValue = *lit->nthArgument(1 - onRight); 

    int val = isBoolValue(truthValue);
    if(val < 0){return false; }
    else {positive = (val == lit->polarity());}
    
    Term* constant = appTerm->nthArgument(0)->term()->nthArgument(0)->term();
    Signature::Symbol* symbol = env.signature->getFunction(constant->functor());
    if(symbol->getConst() == Signature::Symbol::EQUALS){
        t1 = *appTerm->nthArgument(0)->term()->nthArgument(1);
        t2 = *appTerm->nthArgument(1);
        return true;
    }
    
    return false;    
}

bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
    CALL("appOfORorIMPorAnd");

  int onRight;
    if(!(isBinaryConstantApp(lit, onRight)))
        return false;

  Term* constant;
 
  Term* appTerm = lit->nthArgument(onRight)->term();
  TermList otherTerm = *lit->nthArgument(1 - onRight);

  int val = isBoolValue(otherTerm); 
  if(val < 0) return false;
   
  constant = appTerm->nthArgument(0)->term()->nthArgument(0)->term();
  Signature::Symbol* symbol = env.signature->getFunction(constant->functor());
  Signature::Symbol::HOLConstant cont = symbol->getConst(); 
  if((cont == Signature::Symbol::AND) && ((val + lit->polarity()) % 2 == 0)) return false;
  if((cont == Signature::Symbol::OR)  && ((val + lit->polarity()) % 2 == 1)) return false;  
  if((cont == Signature::Symbol::IMP) && ((val + lit->polarity()) % 2 == 1)) return false;
  
  lhs1 = *appTerm->nthArgument(0)->term()->nthArgument(1);
  lhs2 = *appTerm->nthArgument(1);
  
  TermList troo = TermList(Term::foolTrue());
  TermList fals = TermList(Term::foolFalse());
   
  switch(cont){ //switching first arg of second app
  case Signature::Symbol::AND:
    rhs1 = fals; rhs2 = fals; //rule for and is t1 = $false \/ t2 = $false ...
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
    
    int onRight;
    if (!isUnaryConstantApp(lit, onRight))
        return false;
  
    TermList appTerm = *lit->nthArgument(onRight); 
    newEqrhs = *lit->nthArgument(1 - onRight);
    newEqlhs = *appTerm.term()->nthArgument(1);
  
    int val = isBoolValue(newEqrhs);
    
    TermList boolValues[] = {TermList(Term::foolFalse()), TermList(Term::foolTrue())};
    
    if(val > -1){
      polarity = true;
      newEqrhs = lit->polarity() ? boolValues[1 - val] : boolValues[val]; //check this AYB
    }else{
      polarity = 1 - lit->polarity();
    }
    
    Term* constant = appTerm.term()->nthArgument(0)->term();
    Signature::Symbol* sym = env.signature->getFunction(constant->functor());
    if(sym->getConst() == Signature::Symbol::NOT){
        return true;
    }               
   
    return false;
}

bool isITerm(TermList term, TermList &t1)
{
  CALL("isITerm");
  
  TermList firstArg = *term.term()->nthArgument(0);
  if(firstArg.isTerm()){
    Signature::Symbol* sym = env.signature->getFunction(firstArg.term()->functor());
    if(sym->getConst() == Signature::Symbol::I_COMB){
      t1 = *term.term()->nthArgument(1);
      return true;  
    }  
  }
  
  return false;
}

bool isKTerm(TermList term, TermList &t1)
{
  CALL("isKTerm");

  TermList firstArg = *term.term()->nthArgument(0);
  if(firstArg.isTerm()){
    Signature::Symbol* sym = env.signature->getFunction(firstArg.term()->functor());
    if(sym->hOLAPP()){
      TermList comb = *firstArg.term()->nthArgument(0);
          if(comb.isTerm()){  
             Signature::Symbol* sym = env.signature->getFunction(comb.term()->functor());
       if(sym->getConst() == Signature::Symbol::K_COMB){
        t1 = *firstArg.term()->nthArgument(1);
          return true;  
       }
      }     
    }  
  }
  
  return false; 
  
}

bool isTenaryCombinatorTerm(TermList term, TermList &t1, TermList &t2, TermList &t3, Signature::Symbol::HOLConstant &combi)
{
  CALL("isTenaryCombinatorTerm");
  
  TermList arg1 = *term.term()->nthArgument(0);
  if(arg1.isTerm()){
    Signature::Symbol* sym = env.signature->getFunction(arg1.term()->functor());
    if(sym->hOLAPP()){
      TermList arg1ofarg1 = *arg1.term()->nthArgument(0);
          if(arg1ofarg1.isTerm()){  
             Signature::Symbol* sym = env.signature->getFunction(arg1ofarg1.term()->functor());
       if(sym->hOLAPP()){
        TermList comb = *arg1ofarg1.term()->nthArgument(0);
          Signature::Symbol* sym = env.signature->getFunction(comb.term()->functor());
          if(sym->getConst() == Signature::Symbol::B_COMB || sym->getConst() == Signature::Symbol::C_COMB ||
           sym->getConst() == Signature::Symbol::S_COMB){
          t1 = *arg1ofarg1.term()->nthArgument(1);
          t2 = *arg1.term()->nthArgument(1);
          t3 = *term.term()->nthArgument(1);
          combi = sym->getConst();
            return true;  
          } 
       }
      }     
    }  
  }
  
  return false; 
  
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
        
                  cout << "-----------------------------" << endl;
  cout << "The premise is : " + c->toString() << endl;
  cout << "The conclusion : " + res->toString() << endl;
  cout << "-----------------------------" << endl;
        
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
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
      
          cout << "-----------------------------" << endl;
  cout << "The premise is : " + c->toString() << endl;
  cout << "The conclusion : " + res->toString() << endl;
  cout << "-----------------------------" << endl;
        
      
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
      Literal *lit = (*c)[i];
      if (isEQUALSApp(lit, lhs, rhs, polarity)) {
        Literal *newLit = Literal::createEquality(polarity, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::HOL_EQUALITY_ELIMINATION, c));//Change inference AYB
        res->setAge(c->age());
        env.statistics->holEQAULSsimplifications++;
        
                  cout << "-----------------------------" << endl;
  cout << "The premise is : " + c->toString() << endl;
  cout << "The conclusion : " + res->toString() << endl;
  cout << "-----------------------------" << endl;
        
        
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
      TermList t1, rhs; 
      bool isTrue, isFalse, isPI;
      unsigned expsrt;
      Literal *lit = (*c)[i];
      if (isPISIGMAapp(lit, t1, rhs, isTrue, isFalse, isPI, expsrt)) {
        Literal *newLit;
        unsigned maxVar = 0;
        TermList lhs = t1;
    
        if((isTrue && isPI) || (isPI && !isTrue && !isFalse) || (isFalse && !isPI)){
          DHSet<unsigned> vars;
          c->collectVars(vars);
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
            lhs = TermList(Term::create2(symbol, lhs, newVar));
            expsrt = env.sorts->getFuncSort(expsrt)->getRangeSort();
          }while(!(expsrt == Sorts::SRT_BOOL));                     
        }
        if((isFalse && isPI) || (isTrue && !isPI) || (!isPI && !isTrue && !isFalse)){
          Stack<unsigned> sorts;
          Formula::VarList* vars = t1.freeVariables();
          Formula::VarList::Iterator fvi(vars);
          DHMap<unsigned,unsigned> _varSorts;
          SortHelper::collectVariableSorts(t1.term(), _varSorts);
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
            lhs = TermList(Term::create2(symbol, lhs, skolemFunc));
      
            expsrt = env.sorts->getFuncSort(expsrt)->getRangeSort();
          }while(!(expsrt == Sorts::SRT_BOOL)); 
        }   
        newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL);     
        Clause* res;
        if(isPI){
           res = replaceLit2(c, lit, newLit, new Inference1(Inference::VPI_ELIMINATION, c));//Change inference AYB
        }else{
           res = replaceLit2(c, lit, newLit, new Inference1(Inference::VSIGMA_ELIMINATION, c));//Change inference AYB
        }           
        res->setAge(c->age());
    
        env.statistics->holPISIGMAsimplifications++;
        
          cout << "-----------------------------" << endl;
  cout << "The premise is : " + c->toString() << endl;
  cout << "The conclusion : " + res->toString() << endl;
  cout << "-----------------------------" << endl;
        
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
        unsigned functor = subterm.term()->functor();
        Signature::Symbol* sym = env.signature->getFunction(functor);
        
        if(!(sym->hOLAPP())){
          continue; //only interested in terms which start vAPP(...
        }       
    
        TermList t1, t2, t3;
        DHMap<unsigned,unsigned> _varSorts;
        SortHelper::collectVariableSorts(subterm.term(), _varSorts);
    
        if (isITerm(subterm, t1)) {
          inference = new Inference1(Inference::I_COMBINATOR_ELIMINATION, premise); 
          combinatorTerm = subterm;
          newTerm        = t1;
          goto substitution;
        }
    
        if (isKTerm(subterm, t1)) {
          inference = new Inference1(Inference::K_COMBINATOR_ELIMINATION, premise); 
          combinatorTerm = subterm;   
          newTerm        = t1;
          goto substitution;
        }
    
        Signature::Symbol::HOLConstant comb;
        if (isTenaryCombinatorTerm(subterm, t1, t2, t3, comb)){
          unsigned t1sort  = SortHelper::getResultSort(t1, _varSorts);
          unsigned t2sort  = SortHelper::getResultSort(t2, _varSorts);
          unsigned t3sort  = SortHelper::getResultSort(t3, _varSorts);
          unsigned ranget1 = env.sorts->getFuncSort(t1sort)->getRangeSort();
      
          switch(comb){
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
  
  cout << "-----------------------------" << endl;
  cout << "The premise is : " + premise->toString() << endl;
  cout << "The conclusion : " + conclusion->toString() << endl;
  cout << "-----------------------------" << endl;
  
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
      : _lit(lit),
        _clause(clause),
    _pol(lit->polarity())
    {
 
      CALL("ORIMPANDIFFXORRemovalGIE::SubtermIterator");
    
      int onRight;
      if (isBinaryConstantApp(lit, onRight)) {     
     
        _count = 0;

        TermList otherTermt = *lit->nthArgument((onRight + 1) % 2);
        Term *appTerm = lit->nthArgument(onRight)->term();
        
        int val = isBoolValue(otherTermt);
        if(val < 0) _rhsIsTerm = true;
    
        Term* constant = appTerm->nthArgument(0)->term()->nthArgument(0)->term();
        Signature::Symbol* sym = env.signature->getFunction(constant->functor());
            
        _constant = sym->getConst(); 
        
        if(((_constant == Signature::Symbol::OR || _constant == Signature::Symbol::IMP) && !_rhsIsTerm && (val == _pol)) ||
           ((_constant == Signature::Symbol::AND) && !_rhsIsTerm && (val != _pol)) ||
            (_constant == Signature::Symbol::EQUALS && !_rhsIsTerm) || _constant == Signature::Symbol::S_COMB ||
        _constant == Signature::Symbol::C_COMB || _constant == Signature::Symbol::B_COMB ||
        _constant == Signature::Symbol::K_COMB || _constant == Signature::Symbol::I_COMB)
        {
          _count = 4;
        }else{
          _rhsIsTrue = (val != _pol) && (val > -1);
          _rhsIsFalse = (val == _pol) && (val > -1);
          _terms.push(*appTerm->nthArgument(0)->term()->nthArgument(1));
          _terms.push(*appTerm->nthArgument(1));
          if(_rhsIsTerm){_terms.push(otherTermt);}   
        }
      } else {
        _count = 4;
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {  
       if((  (_constant == Signature::Symbol::AND)  || (_constant == Signature::Symbol::OR)
           ||(_constant == Signature::Symbol::IMP)) && _rhsIsTerm)
              return _count < 3; 

       if((  (_constant == Signature::Symbol::XOR)  || (_constant == Signature::Symbol::IFF))
           && _rhsIsTerm)
              return _count < 4;

       return _count < 2;             
    
    }
    OWN_ELEMENT_TYPE next()
    {
      CALL("ORIMPANDIFFXORRemovalGIE::SubtermIterator::next()");

      TermList boolValues[] = {TermList(Term::foolTrue()), TermList(Term::foolFalse())};
    
      Clause *res;
      Inference *inf;
      if(_constant == Signature::Symbol::EQUALS){     
        inf = new Inference1(Inference::HOL_EQUALITY_ELIMINATION, _clause);   
      }else{
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
           l1 = Literal::createEquality(_count, _terms[0], _terms[1], Sorts::SRT_BOOL);
           l2 = Literal::createEquality(true, _terms[2], boolValues[_count], Sorts::SRT_BOOL);
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
      
      res->setAge(_clause->age()+1);
      
      env.statistics->holBINARYCONNgeneratingrules++;
      return res;
    }
  private:
    unsigned _count;
    Literal* _lit;
    Clause* _clause;
    int _pol;
    bool _rhsIsTerm;
    bool _rhsIsTrue;
    bool _rhsIsFalse;
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
