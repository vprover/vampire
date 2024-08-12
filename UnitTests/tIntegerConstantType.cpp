/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include <iostream>
#include "Lib/List.hpp"
#include "Lib/BitUtils.hpp"
// TODO rename to theory test
#include "Kernel/Theory.hpp"
#include "Lib/Int.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

TEST_FUN(list_1)
{
  IntList* lst = 0;

  IntList::push(0, lst);
  IntList::push(1, lst);

  IntList::DelIterator dit(lst);
  ALWAYS(dit.hasNext());
  ALWAYS(dit.next()==1);
  dit.del();
  ASS_EQ(lst->head(), 0);
  ASS_ALLOC_TYPE(lst, "List");
}

inline auto ict(int i) -> IntegerConstantType { return IntegerConstantType(i); }
inline auto rct(int i) -> RationalConstantType { return RationalConstantType(ict(i)); }
inline auto rct(int i, int j) -> RationalConstantType { return RationalConstantType(ict(i), ict(j)); }

TEST_FUN(test01) {

  for (int i = -512; i <= 512; i++) {
    auto exp = ict(BitUtils::log2(Int::safeAbs(i)));
    auto is = ict(i).abs().log2();
    if (is != exp ) {
      std::cout << "[ fail ] ict(" << i << ").abs().log2()" << std::endl;
      std::cout << "[   is ] " << is << std::endl;
      std::cout << "[  exp ] " << exp << std::endl;
      ASSERTION_VIOLATION
    }
  }
}

TEST_FUN(divides) {

  ASS( ict(  1).divides(ict(15)))
  ASS( ict(  3).divides(ict(15)))
  ASS( ict(  5).divides(ict(15)))
  ASS( ict( -1).divides(ict(15)))
  ASS( ict( -3).divides(ict(15)))
  ASS( ict( -5).divides(ict(15)))

  ASS( ict(  3).divides(ict(-15)))
  ASS( ict(  5).divides(ict(-15)))
  ASS( ict(  1).divides(ict(-15)))
  ASS( ict( -1).divides(ict(-15)))
  ASS( ict( -3).divides(ict(-15)))
  ASS( ict( -5).divides(ict(-15)))

  ASS(!ict(  7).divides(ict(15)))
  ASS(!ict( -7).divides(ict(15)))
  ASS(!ict( 15).divides(ict(3)))
  ASS(!ict(-15).divides(ict(3)))

}

TEST_FUN(floor) {
  ASS_EQ( rct(3,5).floorRat(), rct(0) )
  ASS_EQ( rct(7,5).floorRat(), rct(1) )
  ASS_EQ( rct(10,5).floorRat(), rct(2) )
  ASS_EQ( rct(12,5).floorRat(), rct(2) )

  ASS_EQ( rct(-12,5).floorRat(), rct(-3) )
  ASS_EQ( rct(-10,5).floorRat(), rct(-2) )
  ASS_EQ( rct( -7,5).floorRat(), rct(-2) )
  ASS_EQ( rct( -3,5).floorRat(), rct(-1) )
}

TEST_FUN(ceiling) {
  ASS_EQ( rct(3,5).ceiling(), rct(1) )
  ASS_EQ( rct(7,5).ceiling(), rct(2) )
  ASS_EQ( rct(10,5).ceiling(), rct(2) )
  ASS_EQ( rct(12,5).ceiling(), rct(3) )

  ASS_EQ( rct(-12,5).ceiling(), rct(-2) )
  ASS_EQ( rct(-10,5).ceiling(), rct(-2) )
  ASS_EQ( rct( -7,5).ceiling(), rct(-1) )
  ASS_EQ( rct( -3,5).ceiling(), rct( 0) )
}

TEST_FUN(precedence) {
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict(-1)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict( 3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict(-1), ict( 3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict(-3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict(-1), ict(-3)))
}
