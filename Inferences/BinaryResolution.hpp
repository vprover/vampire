/**
 * @file BinaryResolution.hpp
 * Defines class BinaryResolution
 *
 */

#ifndef __BinaryResolution__
#define __BinaryResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BinaryResolution
: public GeneratingInferenceEngine
{
public:
  BinaryResolution() : _index(0) {}

  /**
   * Create BinaryResolution rule with explicitely provided index,
   * independent of an SaturationAlgorithm.
   *
   * For objects created by this constructor, methods  @c attach()
   * and @c detach() must not be called.
   */
  BinaryResolution(GeneratingLiteralIndex* index) : _index(index) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  static Clause* generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult res, Limits* limits=0);
  ClauseIterator generateClauses(Clause* premise);

private:
  struct UnificationsFn;
  struct ResultFn;

  GeneratingLiteralIndex* _index;
};

};

#endif /*__BinaryResolution__*/
