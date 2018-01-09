/*
 * File Induction 
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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "Lib/Array.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"


#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Induction.hpp"

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 


TermList ConstantReplacement::transformSubterm(TermList trm)
{
  CALL("ConstantReplacement::transformSubterm");

  if(trm.isTerm() && trm.term()->functor()==_f){
   return _r;
  }
  return trm;
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise));
}

InductionClauseIterator::InductionClauseIterator(Clause* premise)
{
  CALL("InductionClauseIterator::InductionClauseIterator");

  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::STRUCTURAL;
  static bool mathInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::MATHEMATICAL;

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);

  if(premise->length()==1 && (all || ( (goal || goal_plus) && premise->isGoal())) )
  {
    Literal* lit = (*premise)[0];

     // TODO change to allow for positive occurence of <
    if(lit->isNegative() && lit->ground()){

      Set<unsigned> ta_constants;
      Set<unsigned> int_constants;
      TermFunIterator it(lit);
      it.next(); // to move past the lit symbol
      while(it.hasNext()){
        unsigned f = it.next();
        if(env.signature->functionArity(f)==0 &&
           (
               all
            || env.signature->getFunction(f)->inGoal()
            || (goal_plus && env.signature->getFunction(f)->inductionSkolem())
           )
        ){
         if(structInd && env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result())){
            ta_constants.insert(f);
          }
          if(mathInd && env.signature->getFunction(f)->fnType()->result()==Sorts::SRT_INTEGER){
            int_constants.insert(f);
          }
        }
      }
      Set<unsigned>::Iterator citer1(int_constants);
      while(citer1.hasNext()){
        unsigned c = citer1.next();
        performMathInduction(premise,lit,c);
      }
      Set<unsigned>::Iterator citer2(ta_constants);
      while(citer2.hasNext()){
        unsigned c = citer2.next();
        //cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;
        static bool one = env.options->structInduction() == Options::StructuralInductionKind::ONE ||
                          env.options->structInduction() == Options::StructuralInductionKind::ALL; 
        static bool two = env.options->structInduction() == Options::StructuralInductionKind::ONE ||
                          env.options->structInduction() == Options::StructuralInductionKind::ALL; 

        if(one){
          performStructInductionOne(premise,lit,c);
        }
        if(two){
          performStructInductionTwo(premise,lit,c);
        }
      } 
    }
  }
}

      // deal with integer constants
      // introduce new clauses per eligable constant:
      // L[zero] | L[fresh+1] | L[fresh-1] 
      // L[zero] | L[fresh+1] | c<0
      // L[zero] | ~[fresh] 
      // where fresh is a fresh constant
void InductionClauseIterator::performMathInduction(Clause* premise, Literal* lit, unsigned c)
{
  CALL("InductionClauseIterator::performMathInduction");

        //cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;

        // create fresh
        unsigned freshS = env.signature->addSkolemFunction(0);
        Signature::Symbol* symbol = env.signature->getFunction(freshS);
        symbol->setType(OperatorType::getConstantsType(Sorts::SRT_INTEGER));
        symbol->markInductionSkolem();
        TermList fresh(Term::createConstant(freshS));

        TermList zero(theory->representConstant(IntegerConstantType(0)));
        TermList one(theory->representConstant(IntegerConstantType(1)));
        TermList mone(theory->representConstant(IntegerConstantType(-1)));

        // create L[zero]
        ConstantReplacement cr1(c,zero);
        Literal* Lzero = cr1.transform(lit);

        // create L[fresh+1]
        TermList fpo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),fresh,one));
        ConstantReplacement cr2(c,fpo);
        Literal* Lfpo = cr2.transform(lit);

        // create L[fresh-1]
        TermList fpmo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),fresh,mone));
        ConstantReplacement cr3(c,fpmo);
        Literal* Lfpmo = cr3.transform(lit);

        // create ~L[fresh]
        ConstantReplacement cr4(c,fresh);
        Literal* nLfresh = Literal::complementaryLiteral(cr4.transform(lit));

        // create c<0
        Literal* cLz = Literal::create2(env.signature->getInterpretingSymbol(Theory::INT_LESS),true,TermList(Term::createConstant(c)),zero);

        // put it all together i.e. create three clauses
        // L[zero] | L[fresh+1] | L[fresh-1] 
        // L[zero] | L[fresh+1] | c<0
        // L[zero] | ~L[fresh] 
        Inference* inf1 = new Inference1(Inference::INDUCTION,premise);
        Inference* inf2 = new Inference1(Inference::INDUCTION,premise);
        Inference* inf3 = new Inference1(Inference::INDUCTION,premise);
        Clause* r1 = new(3) Clause(3,premise->inputType(),inf1);
        Clause* r2 = new(3) Clause(3,premise->inputType(),inf2);
        Clause* r3 = new(2) Clause(2,premise->inputType(),inf3);

        (*r1)[0] = Lzero;
        (*r1)[1] = Lfpo; 
        (*r1)[2] = Lfpmo;

        (*r2)[0] = Lzero;
        (*r2)[1] = Lfpo;
        (*r2)[2] = cLz;

        (*r3)[0] = Lzero;
        (*r3)[1] = nLfresh;

        _clauses.push(r1);
        _clauses.push(r2);
        _clauses.push(r3);

 }

      // Now deal with term algebra constants
      // introduce new clauses per eligable constant:
      // L[b1] | ... | L[bn] | ~L[kx1]
      // L[b1] | ... | L[bn] | L[c1[..xi...]] | ... L[cm[...xi...]]
      // where kxn are fresh constants

void InductionClauseIterator::performStructInductionOne(Clause* premise, Literal* lit, unsigned c)
{
  CALL("InductionClauseIterator::performStructInductionOne"); 

        TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(c)->fnType()->result());
        unsigned ta_sort = ta->sort();

        //TODO don't think I need this
        //Array<Stack<TermList>> skolemTerms(env.sorts->count());
        //but this instead
        Stack<TermList> skolemTerms;
        //and probably this here
        unsigned vars = 0;

        Stack<Literal*> baseLits;
        Stack<Literal*> conLits;

        for(unsigned i=0;i<ta->nConstructors();i++){
          TermAlgebraConstructor* con = ta->constructor(i);

          // if a base constructor then construct L[base]
          if(con->arity()==0){
            TermList cont(Term::createConstant(con->functor()));
            ConstantReplacement cr(c,cont);
            baseLits.push(cr.transform(lit));
          }
          // otherwise construct L[con(xn)] e.g. L[cons(i,xn)]
          else{
            // first create the new term
            // need to quantify & skolemize over the missing bits of the constructor
            // TODO actually... no I don't, they should be variables
            Stack<TermList> argTerms; 
            //ZIArray<unsigned> skolemIndex(env.sorts->count());
            unsigned skolems = 0;
            for(unsigned i=0;i<con->arity();i++){
              unsigned srt = con->argSort(i);

              if(srt == ta_sort){
                if(skolemTerms.size() <= skolems){
                  unsigned xn = env.signature->addSkolemFunction(0);
                  Signature::Symbol* symbol = env.signature->getFunction(xn);
                  symbol->setType(OperatorType::getConstantsType(srt));
                  symbol->markInductionSkolem();
                  skolemTerms.push(TermList(Term::createConstant(xn)));
                } 
                ASS(skolemTerms.size() > skolems); 
                argTerms.push(skolemTerms[skolems]);
                skolems++;
              }
              else{
                argTerms.push(TermList(vars,false)); 
                vars++;
              }

            }
            TermList cont(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
            ConstantReplacement cr(c,cont);
            conLits.push(cr.transform(lit));
          }
        }

        Stack<Literal*> xfnLits;

        Stack<TermList>::Iterator xnit(skolemTerms);
        while(xnit.hasNext()){
          // construct ~L[x1]
          TermList xnt = xnit.next();
          ConstantReplacement crX(c,xnt);
          Literal* nLxn = Literal::complementaryLiteral(crX.transform(lit));
          xfnLits.push(nLxn);
        }

      // now create
      // L[b1] | ... | L[bn] | ~L[xi]
      // L[b1] | ... | L[bn] | L[c1[..xi...]] | ... L[cm[...xi...]]
    
        // L[b1] | ... | L[bn] | ~L[xi] 
      {
        Stack<Literal*>::Iterator xnit(xfnLits);
        while(xnit.hasNext()){

          Literal* xnlit = xnit.next();
          Inference* inf = new Inference1(Inference::INDUCTION,premise);
          unsigned size = baseLits.size()+1;
          Clause* r = new(size) Clause(size,premise->inputType(),inf);

          (*r)[0] = xnlit;

          unsigned i = 1;
          Stack<Literal*>::Iterator bit(baseLits);
          while(bit.hasNext()){
            Literal* blit = bit.next();
            (*r)[i] = blit;
            i++;
          }

          _clauses.push(r);
        }
      }

      //  L[b1] | ... | L[bn] | L[c1[..xi...]] | ... L[cm[...xi...]]
      {
          Inference* inf = new Inference1(Inference::INDUCTION,premise);
          unsigned size = conLits.size()+baseLits.size();
          Clause* r = new(size) Clause(size,premise->inputType(),inf);
  
          unsigned i=0;
          for(;i<conLits.size();i++){ 
            (*r)[i]= conLits[i]; 
          }
          for(unsigned j=0;j<baseLits.size();j++){
            ASS(i<size);
            (*r)[i] = baseLits[j]; 
            i++;
          }
 
          _clauses.push(r);


      }
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * Remember! that lit is (by construction) a negative literal... so lit = !L and we're talking about the
 * smallest k that makes L[k] false
 *
 * The clauses we generate are (where L is lit here)
 * L[k]
 * k != con1(...d1(k)...d2(k)...) | ~L[d1(k)] 
 * k != con1(...d1(k)...d2(k)...) | ~L[d2(k)] 
 * k != con2( ...
 * ...
 *
 *
 */
void InductionClauseIterator::performStructInductionTwo(Clause* premise, Literal* lit, unsigned c)
{

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(c)->fnType()->result());
  unsigned ta_sort = ta->sort();

  unsigned sk = env.signature->addSkolemFunction(0);
  Signature::Symbol* symbol = env.signature->getFunction(sk);
  symbol->setType(OperatorType::getConstantsType(ta_sort));
  symbol->markInductionSkolem();
  TermList skt = TermList(Term::createConstant(sk));

  // make L[k]
  {
    ConstantReplacement cr(c,skt);
    Clause* r = new(1) Clause(1,premise->inputType(),new Inference1(Inference::INDUCTION,premise));
    (*r)[0] = cr.transform(lit);
    _clauses.push(r);
  }

  // make 
  //
  // k != con1(...d1(k)...d2(k)...) | ~L[d1(k)] 
  // k != con1(...d1(k)...d2(k)...) | ~L[d2(k)] 
  // ..
  //
  // for each coni
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
  
    // ignore a constructor if it doesn't mention ta_sort
    bool ignore = (arity == 0);
    for(unsigned j=0;j<arity && ignore; j++){ ignore &= (con->argSort(j)!=ta_sort); } 

    if(!ignore){
  
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djk(Term::create1(dj,skt));
        argTerms.push(djk);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djk);
        }
      }
      // create k != con1(...d1(k)...d2(k)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(false,skt,coni,ta_sort);
      // now create the clauses
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        TermList djk = tit.next();
        Clause* r = new(2) Clause(2,premise->inputType(),new Inference1(Inference::INDUCTION,premise));
        (*r)[0] = kneq;
        ConstantReplacement cr(c,djk);
        (*r)[1] = Literal::complementaryLiteral(cr.transform(lit));
        _clauses.push(r);
      }
    }
  }
}

}
