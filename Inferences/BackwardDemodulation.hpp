/**
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __BackwardDemodulation__
#define __BackwardDemodulation__

namespace Inferences {

class BackwardDemodulation
: public BackwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, ClauseIterator& toRemove, ClauseIterator& toAdd);
private:
  DemodulationSubtermIndex* _index;
};

};

#endif /* __BackwardDemodulation__ */
