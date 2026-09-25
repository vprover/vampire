/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Debug/Assertion.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Shell/Options.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <iostream>
#include <utility>
#include <vector>

using namespace Kernel;
using namespace Indexing;

namespace {

using Mode = Shell::Options::UnificationWithAbstraction;
using Index = TermSubstitutionTree<TermWithoutValue>;

TypedTermList typed(TermSugar term)
{
  return TypedTermList(term.sugaredExpr(), term.sort());
}

void expectOrdinaryUnifier(Mode mode, TermList left, TermList right)
{
  std::cout << "UWA ordinary mode=" << mode << " left=" << left
            << " [bank 0] right=" << right << " [bank 1]" << std::endl;
  auto result = AbstractingUnifier::unify(left, 0, right, 1,
                                        AbstractionOracle(mode), false);
  ASS(result);
  ASS(result->constr().isEmpty());
  ASS_EQ(result->subs().apply(left, 0), result->subs().apply(right, 1));
}

void reflexiveIndexMatrix(Mode mode)
{
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat)
  DECL_CONST(b, Rat)
  DECL_FUNC(f, {Rat}, Rat)
  DECL_FUNC(g, {Rat}, Rat)

  const std::vector<TypedTermList> terms = {
    typed(a), typed(b), typed(num(0)), typed(num(1)),
    typed(f(a)), typed(f(num(1))), typed(g(a)), typed(a + num(1))
  };
  for (const auto& term : terms) {
    ASS(term.ground());
    expectOrdinaryUnifier(mode, term, term);
  }

  // Several top symbols force actual index branching. The reversed insertion
  // order checks that the exact match does not depend on which branch is first.
  for (bool reverse : {false, true}) {
    auto inserted = terms;
    if (reverse) {
      std::reverse(inserted.begin(), inserted.end());
    }
    Index index;
    for (const auto& term : inserted) {
      index.insert(TermWithoutValue(term));
    }
    for (const auto& query : terms) {
      unsigned exactMatches = 0;
      std::cout << "UWA exact mode=" << mode << " reverse=" << reverse
                << " query=" << query << std::endl;
      for (auto qr : iterTraits(index.getUwa(query, mode, false, false))) {
        // Abstraction can also return constrained matches for other terms.
        // Only the identical inserted term has this unconditional contract.
        if (qr.data->term == query) {
          ++exactMatches;
          auto constraints = qr.unifier->computeConstraintLiterals();
          ASS(constraints->isEmpty());
          ASS_EQ(qr.unifier->subs().apply(query, subsTreeQueryBank(0)), query.untyped());
          ASS_EQ(qr.unifier->subs().apply(qr.data->term, subsTreeInternalBank(0)), query.untyped());
        }
      }
      ASS_EQ(exactMatches, 1u);
    }
  }
}

void variableBankMatrix(Mode mode)
{
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat)
  DECL_FUNC(f, {Rat}, Rat)
  DECL_VAR_SORTED(x, 0, Rat)

  const auto variable = typed(x).untyped();
  for (auto term : {typed(a).untyped(), typed(f(a)).untyped(), typed(f(x)).untyped()}) {
    expectOrdinaryUnifier(mode, variable, term);
    expectOrdinaryUnifier(mode, term, variable);
  }
  // In the f(x) rows, X0 in the two banks denotes distinct variables.
  // Rejecting these rows as an occurs-check cycle would be incorrect.
}

void sortedVariableIndexMatrix(Mode mode)
{
  NUMBER_SUGAR(Rat)
  DECL_SORT(s)
  DECL_CONST(a, Rat)
  DECL_CONST(c, s)
  DECL_FUNC(f, {Rat}, Rat)
  DECL_FUNC(h, {s}, s)
  DECL_VAR_SORTED(xRat, 0, Rat)
  DECL_VAR_SORTED(xOther, 0, s)

  const std::vector<TypedTermList> terms = {
    typed(a), typed(f(a)), typed(num(0)), typed(xRat),
    typed(c), typed(h(c)), typed(xOther)
  };
  Index index;
  for (const auto& term : terms) {
    index.insert(TermWithoutValue(term));
  }
  for (const auto& query : {typed(xRat), typed(xOther)}) {
    std::vector<unsigned> counts(terms.size(), 0);
    std::cout << "UWA sorted variable mode=" << mode << " query=" << query << std::endl;
    for (auto qr : iterTraits(index.getUwa(query, mode, false, false))) {
      ASS_EQ(qr.data->term.sort(), query.sort());
      const auto position = std::find(terms.begin(), terms.end(), qr.data->term);
      ASS(position != terms.end());
      ++counts[static_cast<std::size_t>(position - terms.begin())];
      auto constraints = qr.unifier->computeConstraintLiterals();
      ASS(constraints->isEmpty());
      ASS_EQ(qr.unifier->subs().apply(query, subsTreeQueryBank(0)),
             qr.unifier->subs().apply(qr.data->term, subsTreeInternalBank(0)));
    }
    for (std::size_t i = 0; i < terms.size(); ++i) {
      ASS_EQ(counts[i], terms[i].sort() == query.sort() ? 1u : 0u);
    }
  }
}

void expectSingleConstraint(Mode mode, TermList left, TermList right, bool ground)
{
  std::cout << "UWA constraint mode=" << mode << " left=" << left
            << " [bank 0] right=" << right << " [bank 1]" << std::endl;
  auto result = AbstractingUnifier::unify(left, 0, right, 1,
                                        AbstractionOracle(mode), false);
  ASS(result);
  auto constraints = result->computeConstraintLiterals();
  ASS_EQ(constraints->size(), 1u);
  const auto literal = (*constraints)[0];
  ASS(literal->isEquality());
  ASS(literal->isNegative());
  ASS_EQ(literal->ground(), ground);
  const auto leftSigma = result->subs().apply(left, 0);
  const auto rightSigma = result->subs().apply(right, 1);
  ASS((literal->termArg(0) == leftSigma && literal->termArg(1) == rightSigma) ||
      (literal->termArg(0) == rightSigma && literal->termArg(1) == leftSigma));
}

void groundConflictMatrix(Mode mode)
{
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat)
  DECL_CONST(b, Rat)
  DECL_FUNC(f, {Rat}, Rat)
  DECL_FUNC(g, {Rat}, Rat)
  const std::vector<std::pair<TypedTermList, TypedTermList>> rows = {
    {typed(a), typed(b)},
    {typed(f(a)), typed(g(b))},
    {typed(f(num(0))), typed(g(num(1)))}
  };
  for (const auto& row : rows) {
    expectSingleConstraint(mode, row.first, row.second, true);
    expectSingleConstraint(mode, row.second, row.first, true);
  }
}



}

TEST_FUN(uwa_off_reflexive_index) { reflexiveIndexMatrix(Mode::OFF); }

TEST_FUN(uwa_ground_reflexive_index) { reflexiveIndexMatrix(Mode::GROUND); }
TEST_FUN(uwa_all_reflexive_index) { reflexiveIndexMatrix(Mode::ALL); }

TEST_FUN(uwa_off_variable_banks) { variableBankMatrix(Mode::OFF); }
TEST_FUN(uwa_constant_variable_banks) { variableBankMatrix(Mode::CONSTANT); }
TEST_FUN(uwa_ground_variable_banks) { variableBankMatrix(Mode::GROUND); }
TEST_FUN(uwa_all_variable_banks) { variableBankMatrix(Mode::ALL); }

TEST_FUN(uwa_off_sorted_variable_index) { sortedVariableIndexMatrix(Mode::OFF); }
TEST_FUN(uwa_constant_sorted_variable_index) { sortedVariableIndexMatrix(Mode::CONSTANT); }
TEST_FUN(uwa_ground_sorted_variable_index) { sortedVariableIndexMatrix(Mode::GROUND); }
TEST_FUN(uwa_all_sorted_variable_index) { sortedVariableIndexMatrix(Mode::ALL); }

TEST_FUN(uwa_ground_ground_conflicts) { groundConflictMatrix(Mode::GROUND); }

TEST_FUN(uwa_all_ground_and_open_conflicts)
{
  groundConflictMatrix(Mode::ALL);
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat)
  DECL_FUNC(f, {Rat}, Rat)
  DECL_FUNC(g, {Rat}, Rat)
  DECL_VAR_SORTED(x, 0, Rat)
  expectSingleConstraint(Mode::ALL, typed(f(x)), typed(g(a)), false);
  expectSingleConstraint(Mode::ALL, typed(g(a)), typed(f(x)), false);
}
