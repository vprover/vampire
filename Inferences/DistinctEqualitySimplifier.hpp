/**
 * @file DistinctEqualitySimplifier.hpp
 * Defines class DistinctEqualitySimplifier.
 */

#ifndef __DistinctEqualitySimplifier__
#define __DistinctEqualitySimplifier__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

class DistinctEqualitySimplifier
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
private:
  static bool canSimplify(Clause* cl);
  static bool mustBeDistinct(TermList t1, TermList t2);
  static bool mustBeDistinct(TermList t1, TermList t2, unsigned& grp);
};

}

#endif // __DistinctEqualitySimplifier__
