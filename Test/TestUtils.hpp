
/*
 * File TestUtils.hpp.
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

  /**
   * The ... are len of integers, positive -- positive polarity, negative -- negative polarity.
   */
  static SAT::SATClause* buildSATClause(unsigned len,...);
};

}

#endif // __TestUtils__
