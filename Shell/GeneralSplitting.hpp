/**
 * @file GeneralSplitting.hpp
 * Defines class GeneralSplitting.
 */


#ifndef __GeneralSplitting__
#define __GeneralSplitting__

#include "../Forwards.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Rule for splitting that reduces number of variables in a clause.
 */
class GeneralSplitting
{
public:
  void apply(UnitList*& units);
private:
  bool apply(Clause*& cl, UnitList*& resultStack);

};

};

#endif /* __GeneralSplitting__ */
