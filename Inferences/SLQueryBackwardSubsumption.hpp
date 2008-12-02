/**
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __SLQueryBackwardSubsumption__
#define __SLQueryBackwardSubsumption__

namespace Inferences {

class SLQueryBackwardSubsumption
: public BackwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, ClauseIterator& toRemove, ClauseIterator& toAdd);
private:
  Index* _index;
};

};

#endif /* __SLQueryBackwardSubsumption__ */
