/**
 * @file VirtualIterator.hpp
 * Defines abstract Index class and some other auxiliary classes.  
 */

#ifndef __Indexing_Index__
#define __Indexing_Index__

#include "../Kernel/Forwards.hpp"
#include "../Kernel/MMSubstitution.hpp"
#include "../Lib/Forwards.hpp"
#include "../Lib/SmartPtr.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Lib;

struct SLQueryResult
{
  SLQueryResult(Literal* l, Clause* c, MMSubstitution* s)
  :literal(l), clause(c), substitution(s) {}

  SLQueryResult(Clause* c, MMSubstitution* s)
  :literal(0), clause(c), substitution(s) {}
  
  Literal* literal;
  Clause* clause;
  const MMSubstitution* substitution;
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
