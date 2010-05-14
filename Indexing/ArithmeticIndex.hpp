/**
 * @file ArithmeticIndex.hpp
 * Defines class ArithmeticIndex.
 */

#ifndef __ArithmeticIndex__
#define __ArithmeticIndex__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Kernel/Theory.hpp"

#include "Index.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ArithmeticIndex
: public Index
{
public:
  ArithmeticIndex();

  void handleClause(Clause* c, bool adding);

private:

  struct ConstraintInfo {
    ConstraintInfo() : hasUpperLimit(false), hasLowerLimit(false) {}

    bool hasUpperLimit;
    bool strongUpperLimit;
    InterpretedType upperLimit;
    Clause* upperLimitPremise;

    bool hasLowerLimit;
    bool strongLowerLimit;
    InterpretedType lowerLimit;
    Clause* lowerLimitPremise;

    CLASS_NAME("ArithmeticIndex::ConstraintInfo");
    USE_ALLOCATOR(ConstraintInfo);
  };

  Theory* theory;
  DHMap<TermList, ConstraintInfo*> _termConstraints;
};

}

#endif // __ArithmeticIndex__
