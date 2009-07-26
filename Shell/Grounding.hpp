/**
 * @file Preprocessor.hpp
 * Defines class Preprocessor.
 */

#ifndef __Grounding__
#define __Grounding__

#include "../Forwards.hpp"

#include "../Lib/VirtualIterator.hpp"

namespace Shell
{

using namespace Kernel;
using namespace Lib;

class Grounding
{
public:
  static ClauseList* simplyGround(ClauseIterator clauses);

private:
  struct GroundingApplicator;
};

}

#endif /* __Grounding__ */
