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
  static bool con = (kind == Options::InductionChoice::CONJECTURE || kind == Options::InductionChoice::CONJECTURE_PLUS);
  static bool inp = (kind == Options::InductionChoice::INPUT || kind == Options::InductionChoice::INPUT_PLUS); 
  static bool plus = (kind == Options::InductionChoice::CONJECTURE_PLUS || kind == Options::InductionChoice::INPUT_PLUS);

  cout << "HERE with " << premise->toString() << endl;
  cout << premise->inputType() << endl;
  if(premise->length()==1 && 
       (kind == Options::InductionChoice::ALL 
     || (con && premise->inputType() != Unit::AXIOM)
     || (inp && premise->inference()->rule() == Inference::INPUT)
     )
     //|| plus) // do check next 
    )
  {
    cout << "inside with " << premise->toString() << endl;
    Literal* lit = (*premise)[0];
/*
    if(plus){
      bool okay = false;
      NonVariableIterator it(lit);
      while(it.hasNext()){
        Term* t = it.next().term();
        if(t->arity()==0 && env.signature->getFunction(t->functor())->inductionSkolem()){
          okay=true;
          break;
        }
      }
      if(!okay){ return; }
    }
    cout << "passed" << endl;
*/

     // TODO change to allow for positive occurence of <
    if(lit->isNegative() && lit->ground()){

      Set<unsigned> ta_constants;
      Set<unsigned> int_constants;
      TermFunIterator it(lit);
      it.next(); // to move past the lit symbol
      while(it.hasNext()){
        unsigned f = it.next();
        if(env.signature->functionArity(f)==0 &&
           (!plus || env.signature->getFunction(f)->inductionSkolem())
        ){
         if(structInd && env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result())){
            ta_constants.insert(f);
          }
          if(mathInd && env.signature->getFunction(f)->fnType()->result()==Sorts::SRT_INTEGER){
            int_constants.insert(f);
          }
        }
      }
      // deal with integer constants
      // introduce new clauses per eligable constant:
      // L[zero] | L[fresh+1] | L[fresh-1] 
      // L[zero] | L[fresh+1] | c<0
      // L[zero] | ~[fresh] 
      // where fresh is a fresh constant
      Set<unsigned>::Iterator citer1(int_constants);
      while(citer1.hasNext()){
        unsigned c = citer1.next();
        cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;

        // create fresh
        unsigned freshS = env.signature->addSkolemFunction(0);
        Signature::Symbol* symbol = env.signature->getFunction(freshS);
        symbol->setType(new FunctionType(Sorts::SRT_INTEGER));
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
        // L[zero] | ~[fresh] 
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
      // L[b1] | L[con1(xf1)] | ... | L[conN(xfn)] 
      // L[b2] | L[con1(xf1)] | ... | L[conN(xfn)] 
      // L[b1] | ~L[xf1] 
      // L[b2] | ~L[xf1] 
      // ...
      // L[b1] | ~L[xfn] 
      // L[b2] | ~L[xfn] 
      // where xn is a fresh constant

      Set<unsigned>::Iterator citer2(ta_constants);
      while(citer2.hasNext()){
        unsigned c = citer2.next();
        cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;

        TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(c)->fnType()->result());
        unsigned ta_sort = ta->sort();

        Array<Stack<TermList>> skolemTerms(env.sorts->sorts());

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
            Stack<TermList> argTerms; 
            ZIArray<unsigned> skolemIndex(env.sorts->sorts());
            for(unsigned i=0;i<con->arity();i++){
              unsigned srt = con->argSort(i);

              if(skolemTerms[srt].size()<skolemIndex[srt]+1){         
                unsigned xn = env.signature->addSkolemFunction(0);
                Signature::Symbol* symbol = env.signature->getFunction(xn);
                symbol->setType(new FunctionType(srt));
                symbol->markInductionSkolem();
                skolemTerms[srt].push(TermList(Term::createConstant(xn)));
              }
              ASS(skolemTerms[srt].size() >= skolemIndex[srt]+1);
              argTerms.push(skolemTerms[srt][skolemIndex[srt]]); 
              skolemIndex[srt] = skolemIndex[srt]+1;
            }
            TermList cont(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
            ConstantReplacement cr(c,cont);
            conLits.push(cr.transform(lit));
          }
        }

        Stack<Literal*> xfnLits;

        Stack<TermList>::Iterator xnit(skolemTerms[ta_sort]);
        while(xnit.hasNext()){
          // construct ~L[xn]
          TermList xnt = xnit.next();
          ConstantReplacement crX(c,xnt);
          Literal* nLxn = Literal::complementaryLiteral(crX.transform(lit));
          xfnLits.push(nLxn);
        }

      // L[b1] | L[con1(xf1)] | ... | L[conN(xfn)] 
      // L[b2] | L[con1(xf1)] | ... | L[conN(xfn)] 
      // L[b1] | ~L[xf1] 
      // L[b2] | ~L[xf1] 
      // ...
      // L[b1] | ~L[xfn] 
      // L[b2] | ~L[xfn] 
    
      // For each zero-arity constructor
      Stack<Literal*>::Iterator bit(baseLits);
      while(bit.hasNext()){
        Literal* blit = bit.next();

        // one clause for the non-zero constructors
        {
          Inference* inf = new Inference1(Inference::INDUCTION,premise);
          unsigned size = conLits.size()+1;
          Clause* r = new(size) Clause(size,premise->inputType(),inf);
          for(unsigned i=0;i<conLits.size();i++){ (*r)[i]= conLits[i]; }
          (*r)[size-1]=blit;
          _clauses.push(r);
        }

        // a clause each for the skolems the constructors use
        Stack<Literal*>::Iterator xnit(xfnLits);
        while(xnit.hasNext()){
          Literal* xnlit = xnit.next();
          Inference* inf = new Inference1(Inference::INDUCTION,premise);
          Clause* r = new(2) Clause(2,premise->inputType(),inf);
          (*r)[0]=xnlit;
          (*r)[1]=blit;
          _clauses.push(r);
        }
      }
    }
    }
  }
}

}
