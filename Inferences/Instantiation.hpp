/**
 * @file Instantiation.hpp
 * Defines class Instantiation
 * @author Giles
 */

#ifndef __Instantiation__
#define __Instantiation__

#include "Forwards.hpp"
#include "Lib/Set.hpp"

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

  void registerClause(Clause* cl);

private:
  VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,unsigned sort);
  class AllSubstitutionsIterator;
  struct ResultFn;

  DHMap<unsigned,Lib::Set<Term*>*> sorted_candidates;

};

};

#endif /*__Instantiation__*/
