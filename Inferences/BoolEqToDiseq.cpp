/*
 * File PrimitiveInstantiation.cpp.
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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/Sorts.hpp"
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



ClauseIterator BoolEqToDiseq::generateClauses(Clause* cl)
{
  CALL("PrimitiveInstantiation::generateClauses");

  unsigned pos = 0;
  Literal* newLit = 0;

  for(unsigned i = 0; i < cl->length(); i++){
    Literal* lit = (*cl)[i];
    if(!lit->polarity()){
      continue;
    }
    TermList eqSort = SortHelper::getEqualityArgumentSort(lit);
    if(eqSort == Term::boolSort()){
      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);
      if(isBool(lhs) || isBool(rhs)){
        continue;
      }
      TermList head = ApplicativeHelper::getHead(lhs);
      if(!head.isVar()){
        Signature::Symbol* sym = env.signature->getFunction(head.term()->functor());
        if(sym->proxy() != Signature::NOT){
          TermList vNot = TermList(Term::createConstant(env.signature->getNotProxy()));
          TermList vNotSort = SortHelper::getResultSort(vNot.term());
          TermList newLhs = ApplicativeHelper::createAppTerm(vNotSort, vNot, lhs);
          newLit = Literal::createEquality(false, newLhs, rhs, Term::boolSort());
          goto afterLoop;
        } 
      }
      head = ApplicativeHelper::getHead(rhs);
      if(!head.isVar()){
        Signature::Symbol* sym = env.signature->getFunction(head.term()->functor());
        if(sym->proxy() != Signature::NOT){
          TermList vNot = TermList(Term::createConstant(env.signature->getNotProxy()));
          TermList vNotSort = SortHelper::getResultSort(vNot.term());
          TermList newRhs = ApplicativeHelper::createAppTerm(vNotSort, vNot, rhs);
          newLit = Literal::createEquality(false, lhs, newRhs, Term::boolSort());
          goto afterLoop;
        } 
      }
    }
    pos++;
  }

  return ClauseIterator::getEmpty(); 

afterLoop:

  Inference* inf = new Inference1(Inference::EQ_TO_DISEQ, cl);

  Clause* res = new(cl->length()) Clause(cl->length(), cl->inputType(), inf);
  res->setAge(cl->age() + 1);

  for (unsigned i = 0; i < res->length(); i++) {
    (*res)[i] = i == pos ? newLit : (*cl)[i];
  }

  return pvi(getSingletonIterator(res));

}

}