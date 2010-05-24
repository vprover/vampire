/**
 * @file TautologyDeletionISE.hpp
 * Defines class TautologyDeletionISE.
 */


#ifndef __TautologyDeletionISE__
#define __TautologyDeletionISE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

class TautologyDeletionISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
private:
  int compare(Literal* l1,Literal* l2);
  void sort(Literal** lits,int to);
};

};

#endif /* __TautologyDeletionISE__ */
