/**
 * @file ClauseSharing.hpp
 * Defines class ClauseSharing.
 */

#ifndef __ClauseSharing__
#define __ClauseSharing__

#include "../Forwards.hpp"

#include "ClauseVariantIndex.hpp"

namespace Indexing 
{

using namespace Kernel;

class ClauseSharing
{
public:
  enum InsertionResult {
    INSERTED,
    OLD_MODIFIED,
    OLD
  };
  Clause* insert(Clause* c, InsertionResult& res);
  void insertNew(Clause* c);
  Clause* tryGet(Literal** lits, unsigned len);
  Clause* tryGet(Clause* c);
private:
  ClauseVariantIndex _index;
};

};

#endif /*__ClauseSharing__*/
