/**
 * @file ClauseSharing.hpp
 * Defines class ClauseSharing.
 */

#ifndef __ClauseSharing__
#define __ClauseSharing__

#include "Forwards.hpp"

#include "ClauseVariantIndex.hpp"

namespace Indexing
{

using namespace Kernel;
using namespace Saturation;

class ClauseSharing
{
public:
  enum InsertionResult {
    INSERTED,
    OLD_MODIFIED,
    OLD,
    ALREADY_THERE
  };

  void init(SaturationAlgorithm* sa);

  bool doSharing(Clause* cl);

  Clause* insert(Clause* c, InsertionResult& res);
  void insertNew(Clause* c);
  Clause* tryGet(Literal* const * lits, unsigned len);
  Clause* tryGet(Clause* c);
private:
  ClauseVariantIndex _index;

  SaturationAlgorithm* _sa;
};

};

#endif /*__ClauseSharing__*/
