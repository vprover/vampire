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

TEST_FUN(underscoreNonAlphaNum_preserves_embedded_nul_and_remaining_bytes)
{
  StringUtils::underscoreNonAlphaNum("seed");
  ASS_EQ(StringUtils::underscoreNonAlphaNum(std::string("a\0-", 3)), std::string("a__", 3));
}

TEST_FUN(underscoreNonAlphaNum_controls)
{
  ASS_EQ(StringUtils::underscoreNonAlphaNum(""), "");
  ASS_EQ(StringUtils::underscoreNonAlphaNum(
    "0!1\"2#3$4%5&6'7(8)9*A+B,C-D.E/F:G;H<I=J>K?L@M[N\\O]P^Q_R`S{T|U}V~WXYZabcdefghijklmnopqrstuvwxyz"),
    "0_1_2_3_4_5_6_7_8_9_A_B_C_D_E_F_G_H_I_J_K_L_M_N_O_P_Q_R_S_T_U_V_WXYZabcdefghijklmnopqrstuvwxyz");
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
