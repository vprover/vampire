/**
 * @file Instantiation.hpp
 * Defines class Instantiation
 * @author Giles
 */

#ifndef __Instantiation__
#define __Instantiation__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;

class Instantiation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Instantiation);
  USE_ALLOCATOR(Instantiation);

  Instantiation() {}

  ClauseIterator generateClauses(Clause* premise);

private:
  VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,unsigned sort);
  class AllSubstitutionsIterator;
  struct ResultFn;

};

};

#endif /*__Instantiation__*/
