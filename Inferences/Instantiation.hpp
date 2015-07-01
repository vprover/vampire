/**
 * @file Instantiation.hpp
 * Defines class Instantiation
 * @author Giles
 */

#ifndef __Instantiation__
#define __Instantiation__

#include "Forwards.hpp"
#include "Lib/Set.hpp"
#include "Kernel/Sorts.hpp"

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
  void expandSort(unsigned sort);
  void expandCandidates(){
    expandSort(Sorts::SRT_INTEGER);
    expandSort(Sorts::SRT_RATIONAL);
    expandSort(Sorts::SRT_REAL);
  }

private:
  bool getRelevantTerms(Clause* cl,unsigned sort, Set<Term*>* candidates);
  VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,unsigned sort);
  class AllSubstitutionsIterator;
  struct ResultFn;

  DHMap<unsigned,Lib::Set<Term*>*> sorted_candidates;

};

};

#endif /*__Instantiation__*/
