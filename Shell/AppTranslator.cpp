
/*
 * File AppTranslator.cpp.
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
 * @file AppTranslator.cpp
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/Tracer.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"


#include "AppTranslator.hpp"

namespace Shell
{

Clause* AppTranslator::translate(Clause* cl)
{
  CALL("AppTranslator::translate(Clause*)");

  for(unsigned i=0;i<cl->length();i++){
    (*cl)[i] = translate((*cl)[i]);
  }

  return cl;
}

Literal* AppTranslator::translate(Literal* lit)
{
  CALL("AppTranslator::translate(Literal*)");
  Stack<TermList> args;
  for(TermList* ts = lit->args(); ts->isNonEmpty(); ts=ts->next()){
    args.push(translate(*ts));
  }
  return Literal::create(lit,args.begin()); 
}

TermList AppTranslator::translate (TermList ts)
{
  CALL("AppTranslator::translate(TermList)");

  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();
  return TermList(translate(term));
} 

TermList getConstantFromFun(unsigned f){
  static DHMap<unsigned,Term*> lookup;
  Term* res = 0; 
  if(!lookup.find(f,res)){
    vstring name = env.signature->getFunction(f)->name() +"c";
    unsigned g = env.signature->addFreshFunction(0,name.c_str());
    res = Term::createConstant(g);
    lookup.insert(f,res);
  }
  return TermList(res); 
}
unsigned getApp(unsigned i){
static DHMap<unsigned,unsigned> lookup;
  unsigned result;
  if(!lookup.find(i,result)){
    result = env.signature->addFreshFunction(2,"app");
    lookup.insert(i,result);
  }
  return result;

}

Term* AppTranslator::translate(Term* term)
{
  CALL("AppTranslator::translate(Term*)");

  unsigned arity = env.signature->functionArity(term->functor());
  if(arity==0){ return term; }

  Stack<TermList> args;
  Term::Iterator terms(term);
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList translatedArgument = translate(argument);
    args.push(translatedArgument);
  }
  Term* result = 0;
  {
    TermList arg_pair[] = { getConstantFromFun(term->functor()), args[0] };
    result = Term::create(getApp(arity),2,arg_pair);
  }
  unsigned i = 1;
  while(i<arity){
   TermList arg_pair[] = { TermList(result), args[i] };
   result = Term::create(getApp(arity-i),2,arg_pair);
   i++;
  }
  return result;
}

}
