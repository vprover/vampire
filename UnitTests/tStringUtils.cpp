/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <array>
#include <string>
#include <vector>

using namespace Lib;

namespace {

// Keep the complete edit graph, independently of StringUtils' rolling row.
size_t editDistanceModel(const std::string& left, const std::string& right)
{
  std::vector<std::vector<size_t>> distance(left.size() + 1,
                                           std::vector<size_t>(right.size() + 1));
  for (size_t i = 0; i <= left.size(); ++i) { distance[i][0] = i; }
  for (size_t j = 0; j <= right.size(); ++j) { distance[0][j] = j; }
  for (size_t i = 1; i <= left.size(); ++i) {
    for (size_t j = 1; j <= right.size(); ++j) {
      distance[i][j] = std::min({distance[i - 1][j] + 1,
                                distance[i][j - 1] + 1,
                                distance[i - 1][j - 1] + (left[i - 1] != right[j - 1])});
    }
  }
  return distance.back().back();
}

void assertStrings(const Stack<std::string>& actual,
                   const std::vector<std::string>& expected)
{
  ASS_EQ(actual.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    ASS_EQ(actual[i], expected[i]);
  }
}

}

TEST_FUN(edit_distance_exhaustive_small_alphabet)
{
  std::vector<std::string> words{""};
  for (unsigned length = 1; length <= 4; ++length) {
    for (unsigned bits = 0; bits < (1U << length); ++bits) {
      std::string word;
      for (unsigned bit = 0; bit < length; ++bit) {
        word += bits & (1U << bit) ? 'b' : 'a';
      }
      words.push_back(word);
    }
  }
  // std::string_view includes NUL bytes; distance must count them as characters.
  words.push_back(std::string("a\0b", 3));
  words.push_back(std::string("\0", 1));
  for (const auto& left : words) {
    for (const auto& right : words) {
      const auto expected = editDistanceModel(left, right);
      ASS_EQ(StringUtils::distance(left, right), expected);
      ASS_EQ(StringUtils::distance(right, left), expected);
    }
  }
  ASS_EQ(StringUtils::distance("kitten", "sitting"), 3);
  ASS_EQ(StringUtils::distance("saturday", "sunday"), 3);
}

TEST_FUN(split_append_empty_fields_and_compaction)
{
  Stack<std::string> values;
  values.push("existing");
  StringUtils::splitStr(",alpha,,beta,", ',', values);
  assertStrings(values, {"existing", "", "alpha", "", "beta", ""});
  StringUtils::dropEmpty(values);
  assertStrings(values, {"existing", "alpha", "beta"});
  StringUtils::dropEmpty(values);
  assertStrings(values, {"existing", "alpha", "beta"});

  values.reset();
  StringUtils::splitStr("", ',', values);
  assertStrings(values, {""});
  StringUtils::dropEmpty(values);
  assertStrings(values, {});
  StringUtils::splitStr("single", ',', values);
  assertStrings(values, {"single"});
  values.reset();
  StringUtils::splitStr("::", ':', values);
  assertStrings(values, {"", "", ""});
  StringUtils::dropEmpty(values);
  assertStrings(values, {});
}

TEST_FUN(equality_fields_and_invalid_structure)
{
  std::string left, right;
  for (const auto& input : {"key=value", "=value", "key=", "="}) {
    ASS(StringUtils::readEquality(input, '=', left, right));
    ASS_EQ(left + "=" + right, input);
  }
  for (const auto& input : {"", "key", "a=b=c"}) {
    ASS(!StringUtils::readEquality(input, '=', left, right));
  }
  ASS(StringUtils::readEquality("left:right", ':', left, right));
  ASS_EQ(left, "left");
  ASS_EQ(right, "right");

  DHMap<std::string, std::string, FnvHash, LengthHash> pairs;
  pairs.set("retained", "old");
  ASS(StringUtils::readEqualities("a=one;b=two;empty=", ';', '=', pairs));
  ASS_EQ(pairs.get("a"), "one");
  ASS_EQ(pairs.get("b"), "two");
  ASS_EQ(pairs.get("empty"), "");
  ASS_EQ(pairs.get("retained"), "old");
  // The API explicitly leaves map contents undefined on failure.
  ASS(!StringUtils::readEqualities("a=one;broken;b=two", ';', '=', pairs));
  ASS(!StringUtils::readEqualities("", ';', '=', pairs));
  ASS(!StringUtils::readEqualities("a=b=c", ';', '=', pairs));
}

TEST_FUN(replacement_literals_overlaps_and_growth)
{
  struct Replacement { std::string input, from, to, expected; };
  const std::array<Replacement, 8> examples{{
    {"", "a", "b", ""},
    {"abc", "", "x", "abc"},
    {"abc", "z", "x", "abc"},
    {"aaaa", "aa", "b", "bb"},
    {"aaaaa", "aa", "", "a"},
    {"aba", "a", "aa", "aabaa"},
    {"one two one", "one", "1", "1 two 1"},
    {std::string("a\0a", 3), "a", "b", std::string("b\0b", 3)}
  }};
  for (const auto& example : examples) {
    auto value = example.input;
    StringUtils::replaceAll(value, example.from, example.to);
    ASS_EQ(value, example.expected);
  }
  ASS_EQ(StringUtils::replaceChar("abracadabra", 'a', '_'), "_br_c_d_br_");
  ASS_EQ(StringUtils::replaceChar("abc", 'z', '_'), "abc");
  ASS_EQ(StringUtils::replaceChar("", 'a', '_'), "");
  ASS_EQ(StringUtils::replaceChar("aaa", 'a', 'a'), "aaa");
}

TEST_FUN(suffix_reserved_characters_and_literal_text)
{
  ASS_EQ(StringUtils::sanitizeSuffix("()\"'$%,."), "________");
  ASS_EQ(StringUtils::sanitizeSuffix("alpha_123"), "alpha_123");
  ASS_EQ(StringUtils::sanitizeSuffix("a(b).c"), "a_b__c");
  ASS_EQ(StringUtils::sanitizeSuffix(""), "");
}

TEST_FUN(numeric_recognition_regular_boundaries)
{
  for (const auto& input : {"0", "1", "9", "10", "12345678901234567890"}) {
    ASS(StringUtils::isPositiveInteger(input));
    ASS(StringUtils::isPositiveDecimal(input));
  }
  for (const auto& input : {"00", "01", "-1", "+1", " 1", "1 ", "a", "1e2"}) {
    ASS(!StringUtils::isPositiveInteger(input));
    ASS(!StringUtils::isPositiveDecimal(input));
  }
  for (const auto& input : {"0.0", "1.25", "999.0001"}) {
    ASS(!StringUtils::isPositiveInteger(input));
    ASS(StringUtils::isPositiveDecimal(input));
  }
  for (const auto& input : {"1.2.3", ".", "-0.1", "0.a"}) {
    ASS(!StringUtils::isPositiveDecimal(input));
  }
}

TEST_FUN(empty_string_is_not_an_integer_numeral)
{
  // SMTLIB2.cpp uses this predicate to recognize numeral tokens and arities.
  // An empty string contains no digits.
  ASS(!StringUtils::isPositiveInteger(""));
}

TEST_FUN(empty_string_is_not_a_decimal_numeral)
{
  ASS(!StringUtils::isPositiveDecimal(""));
}

TEST_FUN(replace_char_preserves_embedded_nul_and_remaining_bytes)
{
  // This API accepts std::string, whose length includes embedded NUL bytes.
  StringUtils::replaceChar("seed", 'x', 'y');
  const std::string input("a\0b", 3);
  const std::string expected("a\0X", 3);
  ASS_EQ(StringUtils::replaceChar(input, 'b', 'X'), expected);
}

TEST_FUN(sanitize_suffix_is_independent_of_previous_calls)
{
  // No NUL normalization policy is assumed. The same input must give the same
  // result regardless of bytes held by a previous call's temporary buffer.
  const std::string input("a\0.", 3);
  StringUtils::sanitizeSuffix("1234");
  const auto first = StringUtils::sanitizeSuffix(input);
  StringUtils::sanitizeSuffix("WXYZ");
  const auto second = StringUtils::sanitizeSuffix(input);
  ASS_EQ(first, second);
}
