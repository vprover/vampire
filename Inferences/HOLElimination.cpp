
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
#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"

#include "HOLElimination.hpp"

namespace Inferences {

unsigned introduceAppSymbol(unsigned sort1, unsigned sort2, unsigned resultSort) {
    
  CALL("HOLElimination::introduceAppSymbol");

  
  Stack<unsigned> sorts;
  sorts.push(sort1); sorts.push(sort2);
  OperatorType* type = OperatorType::getFunctionType(2, sorts.begin(), resultSort);
  unsigned symbol;
  bool added;
  
  vstring srt1 = Lib::Int::toString(sort1);
  vstring srt2 = Lib::Int::toString(sort2);
  symbol = env.signature->addFunction("vAPP_" + srt1 + "_" + srt2, 2, added);

  
  if(added){
   env.signature->getFunction(symbol)->setType(type);
  }

  return symbol;
}


bool isUnaryConstantApp(Literal* lit)
{
    CALL("isUnaryConstantApp");

    if(!lit->isEquality())
        return false;    
    
    TermList lhs = *lit->nthArgument(0);
    
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


bool isBinaryConstantApp(Literal* lit)
{
    CALL("isBinaryConstantApp");
    
    if(!lit->isEquality())
        return false;   
    
    TermList lhs = *lit->nthArgument(0);
        
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







bool isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &rhsIsTrue, bool &rhsIsFalse, bool &isPI,
                  unsigned &srt1, unsigned &srt2)
{
    CALL("isPISIGMAapp");

    if(!isUnaryConstantApp(lit))
       return false;

    TermList lhs = *lit->nthArgument(0); 
    rhs = *lit->nthArgument(1);    	
	
	if(env.signature->isFoolConstantSymbol(true, rhs.term()->functor()))
		 rhsIsTrue = true;
	else rhsIsTrue = false;
    
    if(env.signature->isFoolConstantSymbol(true, rhs.term()->functor()))
		 rhsIsFalse = true;
	else rhsIsFalse = false;
	
    t1 = *lhs.term()->nthArgument(1);
   
    Term* constant = lhs.term()->nthArgument(0)->term();
    Signature::Symbol* sym = env.signature->getFunction(constant->functor());
    if(sym->getConst() == Signature::Symbol::PI ||
	   sym->getConst() == Signature::Symbol::SIGMA ){
		
        isPI = sym->getConst() == Signature::Symbol::PI ? true : false;
		 
		srt1 = sym->fnType()->result();
		srt1 = env.sorts->getFuncSort(srt1)->getRangeSort();
		srt2 = env.sorts->getFuncSort(srt1)->getRangeSort();
        return true;
    }               
    
    return false;   
    
}

bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive)
{
    CALL("isEQUALSApp");

    if(!(isBinaryConstantApp(lit)))
        return false;
    
    TermList rhs = *lit->nthArgument(1); 
    Term* rhst = rhs.term();
    
    bool rightHandSideIsTrue = env.signature->isFoolConstantSymbol(true, rhst->functor());
    bool rightHandSideIsFalse = env.signature->isFoolConstantSymbol(false, rhst->functor());
    
    if(!rightHandSideIsTrue && !rightHandSideIsFalse) 
        return false;
    else 
        positive = rightHandSideIsTrue;
    
    Term* lhst = lit->nthArgument(0)->term();
    Term* constant = lhst->nthArgument(0)->term()->nthArgument(0)->term();
    Signature::Symbol* symbol = env.signature->getFunction(constant->functor());
    if(symbol->getConst() == Signature::Symbol::EQUALS){
        t1 = *lhst->nthArgument(0)->term()->nthArgument(1);
        t2 = *lhst->nthArgument(1);
        return true;
    }
    
    return false;    
}

bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2)
{
    CALL("appOfORorIMPorAnd");

    if(!(isBinaryConstantApp(lit)))
        return false;
    
    TermList rhs = *lit->nthArgument(1); 
    Term* rhst = rhs.term();
    Term* lhst = lit->nthArgument(0)->term();
    
    bool rightHandSideIsTrue = env.signature->isFoolConstantSymbol(true, rhst->functor());
    bool rightHandSideIsFalse = env.signature->isFoolConstantSymbol(false, rhst->functor());
    
    Term* constant = lhst->nthArgument(0)->term()->nthArgument(0)->term();
    lhs1 = *lhst->nthArgument(0)->term()->nthArgument(1);
    lhs2 = *lhst->nthArgument(1);
    
    Signature::Symbol* symbol = env.signature->getFunction(constant->functor());
    switch(symbol->getConst()){ //switching first arg of second app
      case Signature::Symbol::AND:
        if(rightHandSideIsFalse){
            rhs1 = rhs; rhs2 = rhs; //rule for and is t1 = $false \/ t2 = $false ...
            return true;
        }
        break;
      case Signature::Symbol::OR:
        if(rightHandSideIsTrue){
            rhs1 = rhs; rhs2 = rhs;
            return true;
        }
        break;
      case Signature::Symbol::IMP:
        if(rightHandSideIsTrue){
            rhs1 = TermList(Term::foolFalse()); rhs2 = rhs;
            return true;
        }
      default:
        return false;
    }

    return false;    
}


bool isNOTEquality(Literal* lit, TermList &newEqlhs, TermList &newEqrhs)
{
    CALL("isNOTEquality");
	
    if (!isUnaryConstantApp(lit))
        return false;
    
    TermList lhs = *lit->nthArgument(0); 
    newEqrhs = *lit->nthArgument(1);    
    newEqlhs = *lhs.term()->nthArgument(1);
   
    Term* constant = lhs.term()->nthArgument(0)->term();
    Signature::Symbol* sym = env.signature->getFunction(constant->functor());
    if(sym->getConst() == Signature::Symbol::NOT){
        return true;
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
        Clause* res = replaceLit2(c, lit, newLit1, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c), newLit2);//Change inference AYB
        res->setAge(c->age());
        //env.statistics->taDistinctnessSimplifications++;
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
      Literal *lit = (*c)[i];
      if (isNOTEquality(lit, lhs, rhs)) {
        Literal *newLit;
        if(env.signature->isFoolConstantSymbol(true, rhs.term()->functor()) ||
           env.signature->isFoolConstantSymbol(false, rhs.term()->functor())){ 
            newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        }else{
            newLit = Literal::createEquality(false, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        }
        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));//Change inference AYB
        res->setAge(c->age());
        //env.statistics->taDistinctnessSimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  } 

Clause* EQUALSRemovalISE::simplify(Clause* c)
  {
    CALL("NOTRemovalISE::simplify");

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      TermList lhs, rhs, t3;
      bool positive;
      Literal *lit = (*c)[i];
      if (isEQUALSApp(lit, lhs, rhs, positive)) {
        Literal *newLit = Literal::createEquality(positive, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));//Change inference AYB
        res->setAge(c->age());
        //env.statistics->taDistinctnessSimplifications++;
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
      TermList t1, rhs; bool isTrue, isFalse, isPI;
	  unsigned srt1, srt2;
      Literal *lit = (*c)[i];
      if (isPISIGMAapp(lit, t1, rhs, isTrue, isFalse, isPI, srt1, srt2)) {
        Literal *newLit;
		int maxVar = 0;
		if((isTrue && isPI) || (isPI && !isTrue && !isFalse) || (isFalse && !isPI)){
	      Formula::VarList::Iterator fvi(t1.freeVariables());
          while (fvi.hasNext()) {
            int var = fvi.next();
            if (var > maxVar) { maxVar = var;}
          }
		  TermList newVar = TermList(maxVar + 1, false);
          unsigned symbol = introduceAppSymbol(srt1, srt2, Sorts::SRT_BOOL);		  
		  TermList lhs = TermList(Term::create2(symbol, t1, newVar));
          newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL);          		  
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
          symbol = introduceAppSymbol(srt1, srt2, Sorts::SRT_BOOL);
		  
		  TermList lhs = TermList(Term::create2(symbol, t1, skolemFunc));
          newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL);   	  
		}

        Clause* res = replaceLit2(c, lit, newLit, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));//Change inference AYB
        res->setAge(c->age());
        //env.statistics->taDistinctnessSimplifications++;
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
   
  struct ORIMPANDIFFXORRemovalGIE::SubtermIterator
  {
    SubtermIterator(Clause *clause, Literal *lit)
      : _lit(lit),
        _clause(clause)
    {
        
      if (isBinaryConstantApp(lit)) {
        _count = 0;
        TermList rhs = *lit->nthArgument(1); 
        Term* rhst = rhs.term();
        Term* lhst = lit->nthArgument(0)->term();
    
        bool rightHandSideIsTrue = env.signature->isFoolConstantSymbol(true, rhst->functor());
        bool rightHandSideIsFalse = env.signature->isFoolConstantSymbol(false, rhst->functor()); 
        
        if(!rightHandSideIsTrue && !rightHandSideIsFalse)
          _rhsIsTerm = true;
    
        Term* constant = lhst->nthArgument(0)->term()->nthArgument(0)->term();
        Signature::Symbol* sym = env.signature->getFunction(constant->functor());
        
        _constant = sym->getConst(); 
        
        if(((_constant == Signature::Symbol::OR || _constant == Signature::Symbol::IMP) && !_rhsIsTerm && rightHandSideIsTrue) ||
           ((_constant == Signature::Symbol::AND) && !_rhsIsTerm && rightHandSideIsFalse) ||
            (_constant == Signature::Symbol::EQUALS && !_rhsIsTerm))
        {
          _count = 4;
        }else{
          _polarity = rightHandSideIsTrue;
          _terms.push(*lhst->nthArgument(0)->term()->nthArgument(1));
          _terms.push(*lhst->nthArgument(1));
          if(_rhsIsTerm){_terms.push(rhs);}   
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

      Stack<TermList> boolValues;
      boolValues.push(TermList(Term::foolTrue()));
      boolValues.push(TermList(Term::foolFalse()));
      
      Clause *res;
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      Literal* l1 = NULL;
      Literal* l2 = NULL;
      Literal* l3 = NULL;      
      
      switch(_constant){
        case Signature::Symbol::OR:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[1], Sorts::SRT_BOOL);
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[0], Sorts::SRT_BOOL) : NULL; 
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[0], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[1], Sorts::SRT_BOOL);
          }       
          break;
        case Signature::Symbol::AND:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[0], Sorts::SRT_BOOL); 
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1], Sorts::SRT_BOOL) : NULL;          
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[1], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[0], Sorts::SRT_BOOL);
          }       
          break;        
        case Signature::Symbol::IMP:
          if(_count < 2){
            l1 = Literal::createEquality(true, _terms[_count], boolValues[_count], Sorts::SRT_BOOL);  
            l2 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[0], Sorts::SRT_BOOL) : NULL;
          }else{
            l1 = Literal::createEquality(true, _terms[0], boolValues[1], Sorts::SRT_BOOL);
            l2 = Literal::createEquality(true, _terms[1], boolValues[0], Sorts::SRT_BOOL);
            l3 = Literal::createEquality(true, _terms[2], boolValues[1], Sorts::SRT_BOOL);           
          }
          break;
        case Signature::Symbol::IFF:
          if(_polarity || (_rhsIsTerm && _count < 2)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Sorts::SRT_BOOL); 
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1], Sorts::SRT_BOOL) : NULL; 
            break;          
          }
          if(!_polarity || (_rhsIsTerm && _count > 1)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[_count], Sorts::SRT_BOOL);             
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[0], Sorts::SRT_BOOL) : NULL;
            break;
          }       
        case Signature::Symbol::XOR:
          if(_polarity || (_rhsIsTerm && _count < 2)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[_count], Sorts::SRT_BOOL);         
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[0], Sorts::SRT_BOOL) : NULL;
            break;
          }
          if(!_polarity || (_rhsIsTerm && _count > 1)){
            l1 = Literal::createEquality(true, _terms[0], boolValues[_count], Sorts::SRT_BOOL); 
            l2 = Literal::createEquality(true, _terms[1], boolValues[(_count + 1) % 2] , Sorts::SRT_BOOL);                
            l3 = _rhsIsTerm ? Literal::createEquality(true, _terms[2], boolValues[1], Sorts::SRT_BOOL) : NULL; 
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
      //env.statistics->taInjectivitySimplifications++;
      return res;
    }
  private:
    unsigned _count;
    Literal* _lit;
    Clause* _clause;
    bool _rhsIsTerm;
    bool _polarity;
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
