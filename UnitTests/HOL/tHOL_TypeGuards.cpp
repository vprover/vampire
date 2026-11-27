/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * Tests for the recognition of type guards and type-class clauses (HOL::isTypeGuard,
 * HOL::isTypeClassClause), used by -sos type_classes and -type_guard_selection.
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                       \
  DECL_SORT(srt)                              \
  DECL_SORT_BOOL                              \
  DECL_SORT_VAR(alpha, 101)                   \
  TROO                                        \
  FOLS                                        \
  DECL_VAR_SORTED(x, 0, srt)                  \
  DECL_POLY_CONST(cls, 1, Bool)               \
  DECL_POLY_CONST(cls2, 1, Bool)              \
  DECL_CONST(p, Bool)                         \
  DECL_CONST(c, srt)                          \
  DECL_CONST(f, arrow(srt, Bool))

// C(T) = $true / $false and their negations, ground or not
TEST_FUN(guards)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  ASS(HOL::isTypeGuard(cls(srt) == troo))
  ASS(HOL::isTypeGuard(cls(srt) != troo))
  ASS(HOL::isTypeGuard(troo == cls(srt)))
  ASS(HOL::isTypeGuard(cls(alpha) == fols))
  ASS(HOL::isTypeGuard(cls(alpha) != fols))
}

// a propositional constant (no type argument), a predicate with a term argument, ordinary equalities
TEST_FUN(non_guards)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  ASS(!HOL::isTypeGuard(p == troo))
  ASS(!HOL::isTypeGuard(ap(f, c) == troo))
  ASS(!HOL::isTypeGuard(c == x))
  ASS(!HOL::isTypeGuard(cls(srt) == p))
}

TEST_FUN(class_clauses)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  ASS(HOL::isTypeClassClause(clause({ cls(srt) == troo })))
  ASS(HOL::isTypeClassClause(clause({ cls(alpha) != troo, cls2(alpha) == troo })))
  ASS(!HOL::isTypeClassClause(clause({ cls(alpha) != troo, ap(f, c) == troo })))
}
