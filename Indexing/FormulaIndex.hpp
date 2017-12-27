
/*
 * File FormulaIndex.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file FormulaIndex.hpp
 * Defines class FormulaIndex.
 */

#ifndef __FormulaIndex__
#define __FormulaIndex__

#include "Forwards.hpp"

#include "Lib/MapToLIFO.hpp"


#include "Index.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

/**
 * Results of these indexes may not be complete
 */
class FormulaIndex {
public:
  virtual ~FormulaIndex() {}

  virtual FormulaQueryResultIterator getEquivalent(Formula* f) = 0;

  virtual void insert(FormulaUnit* unit, Formula* f) = 0;
  virtual void remove(FormulaUnit* unit, Formula* f) = 0;
};

class StringFormulaIndex : public FormulaIndex {
public:
  virtual FormulaQueryResultIterator getEquivalent(Formula* f);

  virtual void insert(FormulaUnit* unit, Formula* f);
  virtual void remove(FormulaUnit* unit, Formula* f);
private:
  vstring getKey(Formula* f);

  struct Entry
  {
    Entry(FormulaUnit* unit, Formula* formula) : unit(unit), formula(formula) {}

    bool operator==(const Entry& o) const { return unit==o.unit && formula==o.formula; }
    bool operator!=(const Entry& o) const { return !((*this)==o); }

    FormulaUnit* unit;
    Formula* formula;
  };

  struct Entry2QR;

  MapToLIFO<vstring,Entry> _map;
};


}

#endif // __FormulaIndex__
