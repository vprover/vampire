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
  CLASS_NAME(TautologyDeletionISE);
  USE_ALLOCATOR(TautologyDeletionISE);

  TautologyDeletionISE(bool deleteEqTautologies=true) : _deleteEqTautologies(deleteEqTautologies) {}
  Clause* simplify(Clause* cl);
private:
  int compare(Literal* l1,Literal* l2);
  void sort(Literal** lits,int to);

  bool _deleteEqTautologies;
};

};

#endif /* __TautologyDeletionISE__ */
