
/*
 * File BetaReductionEngine.cpp.
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
 * @file BetaReductionEngine.cpp
 * @since 01/04/2018 Manchester
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"
#include "Shell/FOOLElimAlt.hpp"

#include "Indexing/TermSharing.hpp"

#include "BetaReductionEngine.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Initialise a BetaReductionEngine
 */ 
BetaReductionEngine::BetaReductionEngine()  {} // BetaReductionEngine::BetaReductionEngine

Term* BetaReductionEngine::BetaReduce(Term* abstractedTerm, TermList redax)
{
  CALL("BetaReductionEngine::BetaReduce");
  
  //cout << "reducing abstracted term " + abstractedTerm->toString() << endl;
  //cout << "the redax is : " + redax.toString() << endl;
  
  Signature::Symbol* sym = env.signature->getFunction(abstractedTerm->functor());
  ASS_REP(sym->lambda(), abstractedTerm->toString());
  
  unsigned replace = 1;
  Stack<TermList*> toDo;
  Stack<Term*> terms;
  Stack<bool> modified;
  Stack<TermList> args;
  //ASS_REP(toDo.isEmpty(), toDo.top()->toString());
  //ASS(terms.isEmpty());
  //modified.reset();
  //args.reset();

  modified.push(false);
  toDo.push(abstractedTerm->args());

  for (;;) {
    /*
    Stack<Term*>::Iterator tit(terms);
    Stack<TermList*>::Iterator sit(toDo);
    Stack<TermList>::Iterator ait(args);
    Stack<bool>::Iterator bit(modified);
    
    cout << "---------------------------" << endl;
    cout << "The termlists are : " << endl;
    while(sit.hasNext()){
      cout << sit.next()->toString() << endl;
    }
    cout << "---------------------------" << endl;
    
    cout << "---------------------------" << endl;
    cout << "The terms are : " << endl;
    while(tit.hasNext()){
      cout << tit.next()->toString() << endl;
    }
    cout << "---------------------------" << endl;

    cout << "---------------------------" << endl;
    cout << "The args are : " << endl;
    while(ait.hasNext()){
      cout << ait.next().toString() << endl;
    }
    cout << "---------------------------" << endl;
    
    cout << "---------------------------" << endl;
    cout << "The modified are : " << endl;
    while(bit.hasNext()){
      cout << (bit.next() ? "true" : "false") << endl;
    }
    cout << "---------------------------" << endl;
    
    cout << "############END FOR CYCLE##########" << endl;
    
    */
    
    TermList* tt=toDo.pop();
    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();
      if(!orig->hasVarHead()){
        Signature::Symbol* sym = env.signature->getFunction(orig->functor());
        if(sym->lambda()){ replace--; }
      }
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }
      if(!orig->arity()){
        args.push(TermList(env.sharing->insert(orig)));
        continue;        
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    if(!t->hasVarHead()){
      Signature::Symbol* sym = env.signature->getFunction(t->functor());
      if(sym->duBruijnIndex() &&  areEqual(sym->name(), replace)){
        //replace index with appropriately lifted redax
        TermList liftedTerm = FOOLElimAlt::lift(redax, replace - 1, 0);
        if(t->arity()){
          //The is the case index(args list)
          //We assume that the redax is a lambda term
          //with number of prefixing lambdas at lease as many
          //as args in args list
          Term* reducedTerm = liftedTerm.term();
          for(unsigned j = 0; j < t->arity(); j++){
            TermList ts = *(t->nthArgument(j));
            reducedTerm = BetaReduce(reducedTerm, ts); 
          }
          args.push(TermList(reducedTerm));
        }else{
          args.push(liftedTerm);
        }
        modified.setTop(true);
        continue;
      }
      if(sym->duBruijnIndex() &&  FOOLElimAlt::indexGreater(sym->name(), replace)){
        //free index, decrement by one, as now surrounded by one extra lambda.
        vstring newInd = decIndex(sym->name());
        unsigned fun = FOOLElimAlt::addDuBruijnIndex(newInd, sym->fnType());
        Term* newTerm = Term::cloneNonShared(t);     
        newTerm->makeSymbol(fun, t->arity()); 
        terms.push(newTerm);
        modified.setTop(true);        
        modified.push(true);
        toDo.push(newTerm->args());
        continue;
      }      
      if(sym->lambda()){ replace++; }
    }
    
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(), abstractedTerm->arity());

  //original abstracted term being a lambda term must have
  //arity 1. Currently, there is a problem if the abstractedTerm is of 
  //the form lam(X). In that case we want to return X, but X is not 
  //a term.   
  return args.top().term();
  // here we assume, that stack is an array with
  // second topmost element as &top()-1, third at
  // &top()-2, etc...
  /*
  TermList* argLst=&args.top() - (abstractedTerm->arity()-1);
  if (abstractedTerm->isLiteral()) {
    Literal* lit = static_cast<Literal*>(abstractedTerm);
    ASS_EQ(args.size(), lit->arity());
    return Literal::create(lit,argLst);
  }
  return Term::create(abstractedTerm, argLst);
  */
  
}

bool BetaReductionEngine::areEqual(vstring indexName, unsigned replace)
{
  CALL("BetaReductionEngine::areEqual");
  
  int ind = 0;
  Int::stringToInt(indexName.substr(0,indexName.find("_")), ind);
  return (replace == (unsigned)ind);
  
}

vstring BetaReductionEngine::decIndex(vstring index)
{
  CALL("BetaReductionEngine::decIndex");
  
  ASS_REP(index.find("_") > 0, index);
  
  unsigned underpos = index.find("_");
  int ind = 0;
  Int::stringToInt(index.substr(0,underpos), ind);
  return Int::toString(ind - 1) + index.substr(underpos); 
}  
  
