
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
   * Tests whether two terms are equal modulo associativity and commutativity.
   * Whether a method is assoc and commut is checked with `TestUtils::isAC(..)`
   *
   * !!! exponential runtime !!!
   */
  static bool eqModAC(Kernel::TermList lhs, Kernel::TermList rhs);

  /**
   * The ... are len of integers, positive -- positive polarity, negative -- negative polarity.
   */
  static SAT::SATClause* buildSATClause(unsigned len,...);


private:
  /**
   * Tests whether there is a permutation pi s.t. pi(lhs) == rhs, where elements are compared by
   * elemEq(l,r)
   * `List` must provide methods 
   *    - `elem_type operator[](unsigned)` 
   *    - `unsigned size()`
   * `Eq`   must provide methods
   *    - `bool operator(const elem_type&, const elem_type&)`
   */
  template<class List, class Eq> 
  bool permEq(const List& lhs, const List& rhs, Eq elemEq);

  /** returns whether the function f is associative and commutative */
  static bool isAC(Kernel::Theory::Interpretation f);
};

}

#endif // __TestUtils__
