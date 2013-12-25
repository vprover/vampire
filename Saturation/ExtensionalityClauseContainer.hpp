#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

namespace Saturation
{

using namespace Kernel;

class ExtensionalityClauseContainer
{
public:
  ExtensionalityClauseContainer() {}
  void addIfExtensionality(Clause* c);
  void remove(Clause* c);
private:
  ClauseList* _clauses;
  void add(Clause* c);
};

}

#endif /*__ExtensionalityClauseContainer__*/
