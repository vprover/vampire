/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "BoolEqToDiseq.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

typedef ApplicativeHelper AH;

ClauseIterator BoolEqToDiseq::generateClauses(Clause* cl)
{
  CALL("PrimitiveInstantiation::generateClauses");

  unsigned pos = 0;
  Literal* newLit = 0;

  for(unsigned i = 0; i < cl->length(); i++){
    Literal* lit = (*cl)[i];
    if(!lit->polarity()){
      pos++;
      continue;
    }
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort == AtomicSort::boolSort()){
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);
      if(AH::isBool(lhs) || AH::isBool(rhs)){
        pos++;
        continue;
      }
      TermList head = AH::getHead(lhs);
      if(!head.isVar()){
        Signature::Symbol* sym = env.signature->getFunction(head.term()->functor());
        if(sym->proxy() != Signature::NOT){
          TermList vNot = TermList(Term::createConstant(env.signature->getNotProxy()));
          TermList vNotSort = SortHelper::getResultSort(vNot.term());
          TermList newLhs = AH::createAppTerm(vNotSort, vNot, lhs);
          newLit = Literal::createEquality(false, newLhs, rhs, AtomicSort::boolSort());
          goto afterLoop;
        } 
      }
      head = AH::getHead(rhs);
      if(!head.isVar()){
        Signature::Symbol* sym = env.signature->getFunction(head.term()->functor());
        if(sym->proxy() != Signature::NOT){
          TermList vNot = TermList(Term::createConstant(env.signature->getNotProxy()));
          TermList vNotSort = SortHelper::getResultSort(vNot.term());
          TermList newRhs = AH::createAppTerm(vNotSort, vNot, rhs);
          newLit = Literal::createEquality(false, lhs, newRhs, AtomicSort::boolSort());
          goto afterLoop;
        } 
      }
    }
    pos++;
  }

  return ClauseIterator::getEmpty(); 

afterLoop:

  Clause* res = new(cl->length()) Clause(cl->length(), GeneratingInference1(InferenceRule::EQ_TO_DISEQ, cl));

  for (unsigned i = 0; i < res->length(); i++) {
    (*res)[i] = i == pos ? newLit : (*cl)[i];
  }

  return pvi(getSingletonIterator(res));

}

}
