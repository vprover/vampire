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
#include "Kernel/Theory.hpp"
#include "Lib/List.hpp"
#include "Lib/BitUtils.hpp"
// TODO rename to theory test
#include "Kernel/Theory.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

static unsigned safeAbs(const int num)
{
  if(num == std::numeric_limits<int>::min()) { // = -2147483648
    return (unsigned)num; // = 2147483648
  }
  // abs works for all other values
  return std::abs(num);
}

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
    auto exp = ict(BitUtils::log2(safeAbs(i)));
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
  ASS_EQ( rct(3,5).floor(), 0 )
  ASS_EQ( rct(7,5).floor(), 1 )
  ASS_EQ( rct(10,5).floor(), 2 )
  ASS_EQ( rct(12,5).floor(), 2 )

  ASS_EQ( rct(-12,5).floor(), -3 )
  ASS_EQ( rct(-10,5).floor(), -2 )
  ASS_EQ( rct( -7,5).floor(), -2 )
  ASS_EQ( rct( -3,5).floor(), -1 )
}

TEST_FUN(ceiling) {
  ASS_EQ( rct(3,5).ceiling(), 1 )
  ASS_EQ( rct(7,5).ceiling(), 2 )
  ASS_EQ( rct(10,5).ceiling(), 2 )
  ASS_EQ( rct(12,5).ceiling(), 3 )

  ASS_EQ( rct(-12,5).ceiling(), -2 )
  ASS_EQ( rct(-10,5).ceiling(), -2 )
  ASS_EQ( rct( -7,5).ceiling(), -1 )
  ASS_EQ( rct( -3,5).ceiling(), 0 )
}

TEST_FUN(precedence) {
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict(-1)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict( 3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict(-1), ict( 3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict( 1), ict(-3)))
  ASS_EQ(Comparison::LESS, IntegerConstantType::comparePrecedence(ict(-1), ict(-3)))
}

TEST_FUN(inverse_modulo_m) {
  auto max = IntegerConstantType(512);
  for (auto i : range(0, max)) {
    for (auto m : range(1, max)) {
      if (i.gcd(m) == 1) {
        auto oneModM = IntegerConstantType(1).remainderE(m);
        auto inv = i.inverseModulo(m);
        ASS_EQ((i * inv).remainderE(m), oneModM)
      }
    }
  }
}

TEST_FUN(to_string)
{
  for (std::string str : { 
      "1111111111111111111111111111111111111111111",
      "-1111111111111111111111111111111111111111111",
      "1111111189123097123890102111111111111111111",
      }) {
    ASS_EQ(Output::toString(IntegerConstantType::parse(str).unwrap()), str);
  }
}

TEST_FUN(parse_real)
{
  ASS_EQ(RealConstantType::parse("0.123E20"), 
         RealConstantType::parse("12300000000000000000"));
  ASS_EQ(RealConstantType::parse("0.123e20"), 
         RealConstantType::parse("12300000000000000000"));
  ASS_EQ(RealConstantType::parse("0.123E-8"), 
         RealConstantType::parse("0.00000000123"));
  ASS_EQ(RealConstantType::parse("0.123e-8"), 
         RealConstantType::parse("0.00000000123"));
}
