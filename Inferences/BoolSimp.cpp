/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"

#include "Kernel/HOL/SubtermReplacer.hpp"

#include "BoolSimp.hpp"

namespace Inferences {

Clause* BoolSimp::simplify(Clause* premise) {
  TermList subTerm;
  TermList simpedSubTerm;
  unsigned literalPosition = 0;
  unsigned cLen = premise->length();

  while (literalPosition < cLen) {
    Literal *literal = (*premise)[literalPosition];
    // Below should be safe. We can bool simplify a term that contains free indices
    NonVariableNonTypeIterator nvi(literal);

    while (nvi.hasNext()) {
      subTerm = TermList(nvi.next());
      if(SortHelper::getResultSort(subTerm.term()).isBoolSort()){
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

  RStack<Literal*> resLits;
  SubtermReplacer replacer(subTerm, simpedSubTerm, /*liftFree=*/false);

  for (unsigned i = 0; i < premise->length(); i++) {
    resLits->push(i == literalPosition ? replacer.transformLiteral((*premise)[i]) : (*premise)[i]);
  }

  return Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::BOOL_SIMP, premise));
}

bool BoolSimp::areComplements(TermList t1, TermList t2)
{
  static TermStack args;

  auto head = HOL::getHeadAndArgs(t1, args);
  if (head.isProxy(Proxy::NOT) && args[0] == t2) {
    return true;
  }

  head = HOL::getHeadAndArgs(t2, args);
  if (head.isProxy(Proxy::NOT) && args[0] == t1) {
    return true;
  }

  return false;
}

TermList BoolSimp::boolSimplify(TermList term)
{
  namespace HC = HOL::create;

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());
  static TermStack args;

  auto head = HOL::getHeadAndArgs(term, args);

  if(head.isVar()){ return term; }

  switch (env.signature->getFunction(head.term()->functor())->proxy()) {
    case Proxy::AND: {
      ASS(args.size() == 2);
      if(args[1] == fols || args[0] == fols){ return fols; }
      if(args[1] == troo){ return args[0]; } else
      if(args[0] == troo){ return args[1]; }
      if(args[0] == args[1]){ return args[0]; }
      if(areComplements(args[0], args[1])){ return fols; }
      break;
    }
    case Proxy::OR: {
      ASS(args.size() == 2);
      if(args[0] == troo || args[1] == troo){ return troo; }
      if(args[0] == fols){  return args[1]; }else
      if(args[1] == fols){ return args[0]; }
      if(args[0] == args[1]){ return args[0]; }
      if(areComplements(args[0], args[1])){ return troo; }
      break;
    }
    case Proxy::IMP:{
      ASS(args.size() == 2);
      if(args[1] == troo){ return args[0]; }
      if(args[1] == fols){ return troo; }
      if(areComplements(args[0], args[1])){ return args[0]; }
      if(args[0] == args[1]){ return troo; }
      if(args[0] == troo){ return troo; }
      if(args[0] == fols){ return HC::app(HC::neg(), args[1]); }
      break;
    }
    case Proxy::IFF:{
      ASS(args.size() == 2);
      if(args[0] == troo){ return args[1]; } else
      if(args[1] == troo){ return args[0]; }
      if(args[0] == fols){ return HC::app(HC::neg(), args[1]); } else
      if(args[1] == fols){ return HC::app(HC::neg(), args[0]); }
      if(args[0] == args[1]){ return troo; }
      if(areComplements(args[0], args[1])){ return fols; }
      break;
    }
    case Proxy::NOT:{
      ASS(args.size() == 1);
      if(args[0] == troo){ return fols; }
      if(args[0] == fols){ return troo; }
      auto head = HOL::getHeadAndArgs(args[0], args);
      if(head.isProxy(Proxy::NOT)){
        ASS(args.size() == 1);
        return args[0];
      }
      break;
    }
    case Proxy::EQUALS:{
      ASS(args.size() == 2);
      if(args[0] == args[1]){ return troo; }
    }
    default:
      return term;
  }
  return term;

}


}
