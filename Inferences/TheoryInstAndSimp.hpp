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

  ClauseIterator generateClauses(Clause* premise);

private:

  void selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits);
  VirtualIterator<Solution> getSolutions(Stack<Literal*>& theoryLiterals);

  Splitter* _splitter;
  //SAT2F0 _naming;
  //Z3Interfacing* _solver;

};

};

#endif

#endif /*__TheoryInstAndSimp__*/
