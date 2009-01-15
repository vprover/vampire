/**
 * @file BinaryResolution.hpp
 * Defines class BinaryResolution
 *
 */

#ifndef __BinaryResolution__
#define __BinaryResolution__

#include "../Forwards.hpp"

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
  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:
  GeneratingLiteralIndex* _index;
};

};

#endif /*__BinaryResolution__*/
