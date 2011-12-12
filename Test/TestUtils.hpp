/**
 * @file TestUtils.hpp
 * Defines class TestUtils.
 */

#ifndef __TestUtils__
#define __TestUtils__

#include "Forwards.hpp"

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"

namespace Test {

class TestUtils {
public:
  static Kernel::Formula* getUniqueFormula(Kernel::UnitList* units);
  static Kernel::Formula* getUniqueFormula(Api::AnnotatedFormulaIterator afit);
  static Kernel::Formula* getUniqueFormula(Api::Problem prb);
};

}

#endif // __TestUtils__
