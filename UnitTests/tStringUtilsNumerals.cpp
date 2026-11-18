/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/StringUtils.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;

TEST_FUN(empty_string_is_not_an_integer_numeral)
{
  ASS(!StringUtils::isPositiveInteger(""));
}

TEST_FUN(empty_string_is_not_a_decimal_numeral)
{
  ASS(!StringUtils::isPositiveDecimal(""));
}

TEST_FUN(integer_numerals)
{
  for (const auto* str : {"0", "1", "1234567890"}) {
    ASS(StringUtils::isPositiveInteger(str));
  }
  for (const auto* str : {"00", "01", "-1", "+1", "1.0", " 1", "1 ", "1a"}) {
    ASS(!StringUtils::isPositiveInteger(str));
  }
  ASS(!StringUtils::isPositiveInteger(std::string("1\0", 2)));
}

TEST_FUN(decimal_numerals)
{
  for (const auto* str : {"0", "1", "123", "0.0", "12.34"}) {
    ASS(StringUtils::isPositiveDecimal(str));
  }
  for (const auto* str : {"00", "01.2", "-1.0", "+1.0", ".", ".1", "1.2.3", "1a", " 1", "1 "}) {
    ASS(!StringUtils::isPositiveDecimal(str));
  }
  ASS(!StringUtils::isPositiveDecimal(std::string("1.0\0", 4)));
}
