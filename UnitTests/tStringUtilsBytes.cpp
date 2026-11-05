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

TEST_FUN(replace_char_preserves_embedded_nul_and_remaining_bytes)
{
  StringUtils::replaceChar("seed", 'x', 'y');
  ASS_EQ(StringUtils::replaceChar(std::string("a\0b", 3), 'b', 'X'),
      std::string("a\0X", 3));
}

TEST_FUN(replace_char_handles_nul_source_and_target)
{
  ASS_EQ(StringUtils::replaceChar(std::string("\0a\0", 3), '\0', 'X'), "XaX");
  ASS_EQ(StringUtils::replaceChar("aba", 'a', '\0'), std::string("\0b\0", 3));
}

TEST_FUN(replace_char_controls)
{
  ASS_EQ(StringUtils::replaceChar("", 'a', 'b'), "");
  ASS_EQ(StringUtils::replaceChar("banana", 'a', 'o'), "bonono");
  ASS_EQ(StringUtils::replaceChar("abc", 'x', 'y'), "abc");
  ASS_EQ(StringUtils::replaceChar("abc", 'a', 'a'), "abc");
}

TEST_FUN(sanitize_suffix_is_independent_of_previous_calls)
{
  const std::string input("a\0.", 3);
  StringUtils::sanitizeSuffix("1234");
  const auto first = StringUtils::sanitizeSuffix(input);
  StringUtils::sanitizeSuffix("WXYZ");
  const auto second = StringUtils::sanitizeSuffix(input);
  ASS_EQ(first, second);
  ASS_EQ(first, std::string("a\0_", 3));
}

TEST_FUN(sanitize_suffix_handles_boundary_nuls)
{
  ASS_EQ(StringUtils::sanitizeSuffix(std::string("\0.\0", 3)),
      std::string("\0_\0", 3));
  ASS_EQ(StringUtils::sanitizeSuffix(std::string(3, '\0')), std::string(3, '\0'));
}

TEST_FUN(sanitize_suffix_controls)
{
  ASS_EQ(StringUtils::sanitizeSuffix(""), "");
  ASS_EQ(StringUtils::sanitizeSuffix("abc_123"), "abc_123");
  ASS_EQ(StringUtils::sanitizeSuffix("()\"'$%,."), "________");
}
