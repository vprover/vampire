/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"

#include "BoolSimp.hpp"

namespace Inferences {

Clause* BoolSimp::simplify(Clause* premise) {
  CALL("BoolSimp::simplify");

  TermList subTerm;
  TermList simpedSubTerm;
  unsigned literalPosition = 0;
  unsigned cLen = premise->length();

  while (literalPosition < cLen) {
    Literal *literal = (*premise)[literalPosition];
    NonVariableNonTypeIterator nvi(literal);

    while (nvi.hasNext()) {
      subTerm = nvi.next();
      if(SortHelper::getResultSort(subTerm.term()) == AtomicSort::boolSort()){
        simpedSubTerm = boolSimplify(subTerm);
        if(simpedSubTerm != subTerm){
          goto substitution;
        }
      }
    }
    literalPosition++;
  }

  return premise;

substitution:

  unsigned conclusionLength = premise->length();
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength, SimplifyingInference1(InferenceRule::BOOL_SIMP, premise));

  for (unsigned i = 0; i < conclusion->length(); i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], subTerm, simpedSubTerm) : (*premise)[i];
  }

  env.statistics->booleanSimps++;
  return conclusion;
}

bool BoolSimp::areComplements(TermList t1, TermList t2){
  CALL("BoolSimp::areComplements");

  Signature::Symbol* sym;
  static TermStack args;
  TermList head;

  ApplicativeHelper::getHeadAndArgs(t1, head, args);
  if(!head.isVar()){
    sym = env.signature->getFunction(head.term()->functor());
    if(sym->proxy() == Signature::NOT){
      ASS(args.size() == 1);
      if(args[0] == t2){ return true;}
    }
  }

  ApplicativeHelper::getHeadAndArgs(t2, head, args);
  if(!head.isVar()){
    sym = env.signature->getFunction(head.term()->functor());
    if(sym->proxy() == Signature::NOT){
      ASS(args.size() == 1);
      if(args[0] == t1){ return true;}
    }
  }

  return false;
}


TermList BoolSimp::negate(TermList term){
  CALL("BoolSimp::negate");
  
  TermList constant, constSort;

  constant = TermList(Term::createConstant(env.signature->getNotProxy()));
  constSort = SortHelper::getResultSort(constant.term());
  return ApplicativeHelper::createAppTerm(constSort, constant, term);
}

TermList BoolSimp::boolSimplify(TermList term){
  CALL("BoolSimp::boolSimplify");

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());
  static TermStack args;
  TermList head;

  ApplicativeHelper::getHeadAndArgs(term, head, args);

  if(head.isVar()){ return term; }

  Signature::Symbol* sym = env.signature->getFunction(head.term()->functor());
  switch(sym->proxy()){
    case Signature::AND:{
      ASS(args.size() == 2);
      if(args[1] == fols || args[0] == fols){ return fols; }
      if(args[1] == troo){ return args[0]; } else 
      if(args[0] == troo){ return args[1]; }
      if(args[0] == args[1]){ return args[0]; }
      if(areComplements(args[0], args[1])){ return fols; }
      break;
    }
    case Signature::OR:{
      ASS(args.size() == 2);
      if(args[0] == troo || args[1] == troo){ return troo; }
      if(args[0] == fols){  return args[1]; }else
      if(args[1] == fols){ return args[0]; }
      if(args[0] == args[1]){ return args[0]; }
      if(areComplements(args[0], args[1])){ return troo; }  
      break;    
    }
    case Signature::IMP:{
      ASS(args.size() == 2);   
      if(args[1] == troo){ return args[0]; }
      if(args[1] == fols){ return troo; }
      if(areComplements(args[0], args[1])){ return args[0]; }
      if(args[0] == args[1]){ return troo; }
      if(args[0] == troo){ return troo; }
      if(args[0] == fols){ return negate(args[1]); }
      break;
    }
    case Signature::IFF:{
      ASS(args.size() == 2);
      if(args[0] == troo){ return args[1]; } else
      if(args[1] == troo){ return args[0]; } 
      if(args[0] == fols){ return negate(args[1]); } else
      if(args[1] == fols){ return negate(args[0]); } 
      if(args[0] == args[1]){ return troo; }
      if(areComplements(args[0], args[1])){ return fols; }
      break;     
    }
    case Signature::NOT:{
      ASS(args.size() == 1);
      if(args[0] == troo){ return fols; }
      if(args[0] == fols){ return troo; }
      ApplicativeHelper::getHeadAndArgs(args[0], head, args);
      if(!head.isVar()){
        sym = env.signature->getFunction(head.term()->functor());
        if(sym->proxy() == Signature::NOT){
          ASS(args.size() == 1);
          return args[0];
        }
      }
      break;
    }
    case Signature::EQUALS:{
      ASS(args.size() == 2);
      if(args[0] == args[1]){ return troo; }
      /*if(args[0].isTerm() && args[0].term()->ground() && 
         args[1].isTerm() && args[1].term()->ground() &&
         args[0] != args[1]){
        return fols;
      }*/
    }
    default:
      return term;
  }
  return term;

}


}
