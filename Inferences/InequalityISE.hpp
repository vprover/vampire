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
 * @file CombinatorDemodISE.hpp
 * Defines class CombinatorDemodISE.
 */


#ifndef __InequalityISE__
#define __InequalityISE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/MaybeBool.hpp"

namespace Inferences {

class InequalityISE
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InequalityISE);
  USE_ALLOCATOR(InequalityISE);

  // returns true if function can deduce t1 >= t2
  // returns false if function can deduce t1 < t2
  // returns maybe otherwise
  // t1 and t2 must both be of sort $int
  MaybeBool greaterEqual(TermList t1, TermList t2);

  Clause* simplify(Clause* cl);
};

};

#endif /* __CombinatorDemodISE__ */
