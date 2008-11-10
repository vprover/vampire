/**
 * @file VirtualIterator.hpp
 * Defines abstract Index class and some other auxiliary classes.  
 */

#ifndef __Index__
#define __Index__

#include "../Kernel/DoubleSubstitution.hpp"
#include "../Lib/Forward.hpp"

struct SLQueryResult
{
  Literal* literal;
  Clause* clause;
  DoubleSubstitution substitution;
};

typedef VirtualIterator<SLQueryResult> SLQueryResultIterator;

enum IndexType {
  BINARY_RESOLUTION_SUBSTITUTION_TREE
};

class Index
{
  
};

#endif /*__Index__*/
