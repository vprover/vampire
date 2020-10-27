
/*
 * File LinearArithmeticDP.cpp.
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
 * @file LinearArithmeticDP.cpp
 * Implements class LinearArithmeticDP.
 */

#define DLADP 1

#include <sstream>

#include "LinearArithmeticDP.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"


namespace DP
{

LinearArithmeticDP::LinearArithmeticDP() 
{
  CALL("LinearArithmeticDP::LinearArithmeticDP");

}

void LinearArithmeticDP::reset()
{
  CALL("LinearArithmeticDP::reset");

}

/**
 * Add literals based on their structure
 * - if non-ground then ignore
 * - if contains symbols that are not +, -, =, or <, numbers, or numeric constants then ignore
 *
 */
void LinearArithmeticDP::addLiterals(LiteralIterator lits, bool onlyEqualites)
{
  CALL("LinearArithmeticDP::addLiterals");

#if DLADP
  cout << ">> addLiterals" << endl;
#endif
  while(lits.hasNext()) {
    Literal* l = lits.next();
    if(!l->ground()) {
      //for now we ignore non-ground literals
      continue;
    }
#if DLADP
    //cout << "Check " << l->toString() << endl;
#endif
    if(!theory->isInterpretedPredicate(l)) continue;
    SubtermIterator sit(l);
    bool skip = false;
    while(sit.hasNext()){
       // As l is ground we know that this term exists e.g. it's not a variable
       Term* st = sit.next().term(); 
       unsigned fun = st->functor();

       if(env.signature->functionArity(fun) == 0 && Sorts::isNumericSort(SortHelper::getResultSort(st))) continue;
       if(theory->isInterpretedNumber(st)) continue; 
       if(theory->isInterpretedFunction(fun)){
         Interpretation interp = theory->interpretFunction(fun);
         if(theory->isLinearOperation(interp)) continue;

         // We're still linear if this is a multiplication by a numer
         if(interp == Interpretation::INT_MULTIPLY || interp == Interpretation::RAT_MULTIPLY || interp == Interpretation::REAL_MULTIPLY){
           // Again, have to be terms as there are no variables
           Term* left  = st->nthArgument(0)->term();
           Term* right = st->nthArgument(0)->term();
           if(theory->isInterpretedNumber(left) || theory->isInterpretedNumber(right)) continue;
         }
       }
       cout << st->toString() << endl;
       skip = true;
       break;
    }
    if(skip) continue;

    if (!onlyEqualites || (l->isEquality() && l->isPositive())) {
      addLiteral(l);
    }
  }
}

void LinearArithmeticDP::addLiteral(Literal* lit)
{
  CALL("LinearArithmeticDP::addLiteral");

#if DLADP
  cout << "Adding " << lit->toString() << endl;
#endif
}

DecisionProcedure::Status LinearArithmeticDP::getStatus(bool retrieveMultipleCores)
{
  CALL("LinearArithmeticDP::getStatus");

  // Currently just return Satisfiable as this is always safe
  return DecisionProcedure::SATISFIABLE;
}



}
