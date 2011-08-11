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

  void attach(SaturationAlgorithm* salg);
  void detach();

  Clause* generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult res, Limits* limits=0);
  ClauseIterator generateClauses(Clause* premise);

private:
  struct UnificationsFn;
  struct ResultFn;

  GeneratingLiteralIndex* _index;
};

};

#endif /*__BinaryResolution__*/
