
/*
 * File TheoryInstAndSimp.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire 4.2.2 (unstable). It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * uses but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TheoryInstAndSimp.hpp
 * Defines class TheoryInstAndSimp
 *
 */

#ifndef __TheoryInstAndSimp__
#define __TheoryInstAndSimp__

#if VZ3

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Substitution.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

struct Solution{
  Solution(bool s) : status(s) {}
  const bool status;
  Substitution subst;
};


class TheoryInstAndSimp
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(TheoryInstAndSimp);
  USE_ALLOCATOR(TheoryInstAndSimp);

  TheoryInstAndSimp() : _splitter(0) {}
  void attach(SaturationAlgorithm* salg);

  ClauseIterator generateClauses(Clause* premise, bool& premiseRedundant);
  ClauseIterator generateClauses(Clause* premise){
    bool r;
    return generateClauses(premise,r);
  }

  VirtualIterator<Solution> getSolutions(Stack<Literal*>& theoryLiterals,bool guarded=true);

private:

  void selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits,bool forZ3);

  Splitter* _splitter;
  //SAT2F0 _naming;
  //Z3Interfacing* _solver;

};

};

#endif

#endif /*__TheoryInstAndSimp__*/
