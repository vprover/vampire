/**
 * @file FormulaIteExpander.hpp
 * Defines class FormulaIteExpander.
 */

#ifndef __FormulaIteExpander__
#define __FormulaIteExpander__

#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

class FormulaIteExpander {
public:
  FormulaIteExpander() : _defs(0) {}

  void apply(UnitList*& units);
  Unit* apply(Unit* unit, UnitList*& defs);
private:
  Unit* apply(Unit* unit);
  Formula* apply(Formula* f);
  FormulaList* apply(FormulaList* fs);
  Formula* makeBinaryJunction(Connective con, Formula* f1, Formula* f2);
  Formula* introduceDefinition(Formula* f);

  UnitList* _defs;
};

}

#endif // __FormulaIteExpander__
