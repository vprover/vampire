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

class ConstraintDatabase
{
public:
  ConstraintDatabase();

  void handleLiteral(Literal* lit, bool adding, Clause* premise, bool negative=false);

  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise);
  bool isGreater(TermList t, InterpretedType val, Clause*& premise);

  void reset()
  { _termConstraints.reset(); }

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


class ArithmeticIndex
: public Index
{
public:
  ArithmeticIndex();

  void handleClause(Clause* c, bool adding);

  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise)
  { return _db.isNonEqual(t, val, premise); }
  bool isGreater(TermList t, InterpretedType val, Clause*& premise)
  { return _db.isGreater(t, val, premise); }


private:
  ConstraintDatabase _db;
};

}

#endif // __ArithmeticIndex__
