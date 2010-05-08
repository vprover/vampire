/**
 * @file Condensation.hpp
 * Defines class Condensation
 *
 */

#ifndef __Condensation__
#define __Condensation__

#include "../Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * Condensation simplification rule.
 */
class Condensation
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
};

};

#endif /*__Condensation__*/
