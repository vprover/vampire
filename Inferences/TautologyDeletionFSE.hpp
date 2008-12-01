/**
 * @file TautologyDeletionFSE.hpp
 * Defines class TautologyDeletionFSE.
 */


#ifndef __TautologyDeletionFSE__
#define __TautologyDeletionFSE__

#include "../Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

class TautologyDeletionFSE
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
private:
  int compare(Literal* l1,Literal* l2);
  void sort(Literal** lits,int to);
};

};

#endif /* __TautologyDeletionFSE__ */
