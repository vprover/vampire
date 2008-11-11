/**
 * @file VirtualIterator.hpp
 * Defines abstract Index class and some other auxiliary classes.  
 */

#ifndef __Indexing_Index__
#define __Indexing_Index__

#include "../Kernel/Forwards.hpp"
#include "../Kernel/DoubleSubstitution.hpp"
#include "../Lib/Forwards.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;

struct SLQueryResult
{
  SLQueryResult(Literal* l, Clause* c, DoubleSubstitution s)
  :literal(l), clause(c), substitution(s) {}

  SLQueryResult(Clause* c, DoubleSubstitution s)
  :literal(0), clause(c), substitution(s) {}
  
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

};
#endif /*__Indexing_Index__*/
