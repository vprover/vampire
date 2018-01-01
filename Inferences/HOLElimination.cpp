
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
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#include "ANDElimination.hpp"

namespace Inferences {

bool appOfORorIMPorAND(Literal* lit, &lhs1, &rhs1, &lhs2, &rhs2)
{
    CALL("appOfORorIMP");

    if(!lit->isEqaulity())
        return false;
    
    TermList lhs = lit->nthArgument(0);
    TermList rhs = lit->nthArgument(1);
    
    if(!(rhs.isTerm() && (rhs.term() == Term::foolTrue() || rhs.term() == Term::foolFalse())
        return false;
	
	Term* rhst = rhs.term();
    
    if(lhs.isTerm()){
		Term* lhst = lhs.term();
        Symbol* symbol = env.signature->getFunction(lhst->functor());
        if(symbol->isAPP()){ //if lhs is of form vAPP(...
            TermList firstArg = lhst->nthArgument(0);
            if(firstArg.isTerm()){
                Term* fat = firstArg.term();
                symbol = env.signature->getFunction(fat->functor());
                if(symbol->isAPP()){ //if lhs is of form vAPP(vAPP(...
                    firstArg = fat->nthArgument(0);
                    if(firstArg.isTerm()){
                        Term* cont = firstArg.term();
                        symbol = env.signature->getFunction(cont->functor());
                        switch(symbol->getConst()){ //switching first arg of second app
						   case Signature::Symbol::AND:
						    if(rhst == Term::foolFalse){
								rhs1 = rhs; rhs2 = rhs; //rule for and is t1 = $false \/ t2 = $false ...
								break;
							}else{
								return false;
							}
						   case Signature::Symbol::OR:
						    if(rhst == Term::foolTrue){
								rhs1 = rhs; rhs2 = rhs;
								break;
							}else{
								return false;
							}
						  case Signature::Symbol::IMP:
		                    if(rhst == Term::foolTrue){
								rhs1 = TermList(Term::foolFalse); rhs2 = rhs;
								break;
							}else{
								return false;
							}
						  default:
						    return false;
						}
						lhs1 = fat->nthArgument(1); //second argument of second vAPP
						lhs2 = lhst->nthArgument(1); //second argument of first vAPP
                    }
                }
            }
        }
    }
    return false;
    
}


bool isNOTEquality(Literal* lit, &TermList newEqlhs, &TermList newEqrhs)
{
    CALL("isNOTEquality");
    if (!lit->isEqaulity())
        return false;
    
    TermList lhs = lit->nthArgument(0); 
    TermList rhs = lit->nthArgument(1);
    
    if(rhs.isTerm(){
       if(rhs.term() == Term::foolTrue()){
           newEqrhs = Term::foolFalse;
       }else if(rhs.term() == Term::foolFalse()){
           newEqrhs = Term::foolTrue();
       }else{return false;}
    }else{return false;}
    
    
    if (lhs.isTerm()){
        Term* lhst = lhs.term();
        Symbol* sym = env.signature->getFunction(lhst->functor());
        if(sym->isAPP()){
            lhs = lhst->nthArgument(0);
            rhs = lhst->nthArgument(1);
            if(lhs.isTerm()){
                lhst = lhs.term();
                sym = env.signature->getFunction(lhst->functor());
                if(sym->getConst == Signature::Symbol::NOT){
                    newEqlhs = rhs;
                    return true;
                }               
            }
        }
    }
    
    return false;
}

Clause* replaceLit(Clause *c, Literal *a, Literal *b, Inference *inf)
{
    CALL("replaceLit");

    int length = c->length();
    Clause* res = new(length) Clause(length,
                                     c->inputType(),
                                     inf);

    unsigned i = 0;
    while ((*c)[i] != a) { i++; }
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;

    return res;
}

Clause* replaceLitWithTwo(Clause *c, Literal *a, Literal *b, Literal *d , Inference *inf)
{
    CALL("replaceLit");

    int length = c->length();
    Clause* res = new(length + 1) Clause(length + 1,
                                     c->inputType(),
                                     inf);

    unsigned i = 0;
    while ((*c)[i] != a) { i++; }
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;
    (*res)[length] = d; //adding new literals at differrent places...
	//should this be length+1 AYB?
	
    return res;
}

  // copy clause c, with the exception of the ith literal
  Clause* removeLit(Clause *c, unsigned i, Inference *inf)
  {
    CALL("removeLit");

    unsigned length = c->length();
    ASS_GE(i, 0);
    ASS_L(i, length);

    Clause* res = new(length - 1) Clause(length - 1,
                                         c->inputType(),
                                         inf);

    std::memcpy(res->literals(), c->literals(), i * sizeof(Literal*));
    std::memcpy(res->literals() + i, c->literals() + i + 1, (length - i - 1) * sizeof(Literal*));

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
        Clause* res = replaceLitWithTwo(c, lit, newLit1, newLit2, Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));//Change inference AYB
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
        Literal *newLit = Literal::createEquality(true, lhs, rhs, Sorts::SRT_BOOL);//Check this in particular polarity, AYB
        Clause* res = replaceLit(c, lit, newLit, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));//Change inference AYB
        res->setAge(c->age());
        //env.statistics->taDistinctnessSimplifications++;
        return res;
      }
    }

    // no literals of the form app(app(vOR... or app(app(vIMP... were found
    return c;
  } 

}
