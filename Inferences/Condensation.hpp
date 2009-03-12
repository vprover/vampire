/**
 * @file Condensation.hpp
 * Defines class Condensation
 *
 */

#ifndef __Condensation__
#define __Condensation__

#include "../Forwards.hpp"
#include "../Indexing/TermIndex.hpp"

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
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
};

};

#endif /*__Condensation__*/
