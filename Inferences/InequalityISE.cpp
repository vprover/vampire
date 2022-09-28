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
 * @file CombinatorDemodISE.cpp
 * Implements class CombinatorDemodISE.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RapidHelper.hpp"
#include "Kernel/NumTraits.hpp"
#include "Shell/Statistics.hpp"
#include "InequalityISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;


Clause* InequalityISE::simplify(Clause* c)
{
  CALL("InequalityISE::simplify");

  using number = NumTraits<IntegerConstantType>;

  auto getPos = [](Literal* lit, TermList t){
    return (*lit->nthArgument(0) == t) ? 0 : 1;
  };
  
  Stack<std::tuple<Literal*, TermList, unsigned>> numeralInequalities;

  unsigned posOfLitToRemove;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    auto res = number::isLess(lit);
    if(res.isSome()){
      TermList t1 = res.unwrap().first;
      TermList t2 = res.unwrap().second;
      if(t1 == t2){ 
        // could replace syntactic equality with
        // with matchability, but code becomes a lot more bothersome...

        if(lit->polarity()){
          // $less(t1, t1), which is false. can remove literal
          posOfLitToRemove = i;
          goto after_loop;
        }
        // ~$less(t1, t1), which is true. can remove cause
        return 0;
      }  


      auto res2 = RapidHelper::isIntComparisonLit(lit);
      if(res2.isSome()){
        TermList t = res2.unwrap();
       
        unsigned pol1 = lit->polarity();
        unsigned pos1 = getPos(lit,t);
        int num1 = number::tryNumeral(*lit->nthArgument(1 - pos1)).unwrap().toInner();

        for(unsigned j = 0; j < numeralInequalities.size(); j++){
          auto tup = numeralInequalities[j];

          TermList t2 = std::get<1>(tup);
          if(t1 != t2) continue;

          Literal* l2 = std::get<0>(tup);
          unsigned pol2 = l2->polarity();
          unsigned pos2 = getPos(l2, t2);
          int num2 = number::tryNumeral(*l2->nthArgument(1 - pos2)).unwrap().toInner();

          // get both literals into a normal form...

          if(!pol1){
            // either ~(t < m) or ~(m < t)
            num1 = pos1 ? num1 + 1 : num1 - 1; 
            pos1 = !pos1; // swap t and m
          } 

          if(!pol2){
            num2 = pos2 ? num2 + 1 : num2 - 1; 
            pos2 = !pos2; // swap t and m  
          }          

          /*if(pos1 == pos2 && pos1 == 0){
            // t < num1 | t < num2
            posOfLitToRemove = num1 <= num2 ? std::get<2>(tup) : i;   
            goto after_loop;
          }

          if(pos1 == pos2 && pos1 == 1){
            // num1 < t  | num2 < t
            posOfLitToRemove = num1 <= num2 ? i : std::get<2>(tup);   
            goto after_loop;
          } */         

          // num1 < t | t < num2
          // t < num1 | num2 < t
          if(pos1 != pos2){

            int lowerBound = pos1 ? num1 : num2;
            int upperBound = pos1 ? num2 : num1;

            if(lowerBound < upperBound){
              //tautology
              return 0;
            }
          }

        }
       
        numeralInequalities.push(std::make_tuple(lit, t, i));
      }
    }
  }

  return c;

after_loop:

  unsigned len = c->length() - 1;
  Clause* conclusion = new(len) Clause(len,
      SimplifyingInference1(InferenceRule::INEQUALITY_SIMP, c));

  unsigned next = 0;
  for (unsigned i = 0; i < c->length(); i++) {
    if(i != posOfLitToRemove){
      (*conclusion)[next++] = (*c)[i];
    }
  }
  ASS(next == len);

  return conclusion;
}



