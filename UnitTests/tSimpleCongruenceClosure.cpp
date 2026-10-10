/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "DP/SimpleCongruenceClosure.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <array>
#include <iostream>
#include <utility>
#include <vector>

using namespace DP;
using namespace Kernel;
using namespace Lib;

namespace {

struct Node {
  unsigned symbol;
  std::vector<unsigned> arguments;
};

struct Equality {
  unsigned left;
  unsigned right;
  bool positive;
  Literal* literal;
};

struct Context {
  unsigned mask;
  unsigned left;
  unsigned right;
  bool reverse;
};

std::ostream& operator<<(std::ostream& out, const Context& context)
{
  return out << "mask=" << context.mask << " left=" << context.left
             << " right=" << context.right << " reverse=" << context.reverse;
}

// This small reference model uses a Boolean relation, transitive closure and
// the definition of congruence. It has no union-find, currying or proof forest.
class Relation {
public:
  Relation(const std::vector<Node>& terms, const std::vector<Equality>& inputs)
    : _same(terms.size(), std::vector<bool>(terms.size(), false))
  {
    for (unsigned i = 0; i < terms.size(); ++i) {
      _same[i][i] = true;
    }
    for (const auto& input : inputs) {
      if (input.positive) {
        _same[input.left][input.right] = _same[input.right][input.left] = true;
      }
    }
    bool changed;
    do {
      changed = false;
      for (unsigned middle = 0; middle < terms.size(); ++middle) {
        for (unsigned left = 0; left < terms.size(); ++left) {
          for (unsigned right = 0; right < terms.size(); ++right) {
            if (!_same[left][right] && _same[left][middle] && _same[middle][right]) {
              _same[left][right] = true;
              changed = true;
            }
          }
        }
      }
      for (unsigned left = 0; left < terms.size(); ++left) {
        for (unsigned right = 0; right < left; ++right) {
          const auto& a = terms[left];
          const auto& b = terms[right];
          if (_same[left][right] || a.symbol != b.symbol || a.arguments.size() != b.arguments.size()) {
            continue;
          }
          bool equivalentArguments = true;
          for (unsigned i = 0; i < a.arguments.size(); ++i) {
            equivalentArguments = equivalentArguments && _same[a.arguments[i]][b.arguments[i]];
          }
          if (equivalentArguments) {
            _same[left][right] = _same[right][left] = true;
            changed = true;
          }
        }
      }
    } while (changed);
  }

  bool same(unsigned left, unsigned right) const { return _same[left][right]; }

  bool inconsistent(const std::vector<Equality>& inputs) const
  {
    for (const auto& input : inputs) {
      if (!input.positive && same(input.left, input.right)) {
        return true;
      }
    }
    return false;
  }

private:
  std::vector<std::vector<bool>> _same;
};

struct Fixture {
  TermList sort;
  std::vector<TermList> terms;
  std::vector<Node> nodes;
  const std::array<std::pair<unsigned, unsigned>, 8> choices{{
    {0, 1}, {1, 2}, {2, 3}, {4, 5}, {7, 8}, {9, 10}, {11, 12}, {4, 7}
  }};

  Fixture()
  {
    DECL_SORT(s)
    DECL_CONST(a, s)
    DECL_CONST(b, s)
    DECL_CONST(c, s)
    DECL_CONST(d, s)
    DECL_FUNC(f, {s}, s)
    DECL_FUNC(g, {s}, s)
    DECL_FUNC(h, {s, s}, s)
    sort = a.sort();
    const std::vector<TermSugar> expressions{a, b, c, d, f(a), f(b), f(c), g(a), g(b), h(a, b), h(b, a), f(f(a)), f(f(b))};
    for (const auto& term : expressions) {
      terms.push_back(term.sugaredExpr());
    }
    nodes = {{0, {}}, {1, {}}, {2, {}}, {3, {}},
             {4, {0}}, {4, {1}}, {4, {2}}, {5, {0}}, {5, {1}},
             {6, {0, 1}}, {6, {1, 0}}, {4, {4}}, {4, {5}}};
  }

  Equality equality(unsigned left, unsigned right, bool positive = true) const
  {
    return {left, right, positive, Literal::createEquality(positive, terms[left], terms[right], sort)};
  }

  std::vector<Equality> inputs(unsigned mask) const
  {
    std::vector<Equality> result;
    // Register every term before asking for class IDs, as the public API requires.
    for (unsigned i = 0; i < terms.size(); ++i) {
      result.push_back(equality(i, i));
    }
    for (unsigned bit = 0; bit < choices.size(); ++bit) {
      if (mask & (1U << bit)) {
        result.push_back(equality(choices[bit].first, choices[bit].second));
      }
    }
    return result;
  }
};

void add(SimpleCongruenceClosure& actual, const std::vector<Equality>& inputs)
{
  for (const auto& input : inputs) {
    actual.addLiteral(input.literal);
  }
}

void verifyCores(SimpleCongruenceClosure& actual, const Fixture& fixture,
                 const std::vector<Equality>& inputs, Context context = {0, 0, 0, false})
{
  ASS_REP(actual.getUnsatCoreCount() > 0u, context);
  for (unsigned coreIndex = 0; coreIndex < actual.getUnsatCoreCount(); ++coreIndex) {
    LiteralStack core;
    actual.getUnsatCore(core, coreIndex);
    ASS_REP2(core.isNonEmpty(), context, coreIndex);
    std::vector<Equality> coreInputs;
    for (unsigned i = 0; i < core.size(); ++i) {
      auto found = std::find_if(inputs.begin(), inputs.end(),
          [&](const Equality& input) { return input.literal == core[i]; });
      ASS_REP2(found != inputs.end(), context, coreIndex);
      coreInputs.push_back(*found);
    }
    // A core must be a contradictory subset of the original inputs. It need
    // not be minimal and need not have a particular ordering.
    Relation expected(fixture.nodes, coreInputs);
    ASS_REP2(expected.inconsistent(coreInputs), context, coreIndex);
  }
}

// The small cases using this helper have a single minimal contradiction.
// Each listed premise is necessary, and no other input is available. Do not
// require a particular core order or reject repeated premises.
void verifyNecessaryPremises(SimpleCongruenceClosure& actual,
                             const std::vector<Literal*>& premises)
{
  ASS_G(actual.getUnsatCoreCount(), 0u);
  for (unsigned coreIndex = 0; coreIndex < actual.getUnsatCoreCount(); ++coreIndex) {
    LiteralStack core;
    actual.getUnsatCore(core, coreIndex);
    for (unsigned i = 0; i < core.size(); ++i) {
      ASS(std::find(premises.begin(), premises.end(), core[i]) != premises.end());
    }
    for (Literal* premise : premises) {
      bool present = false;
      for (unsigned i = 0; i < core.size(); ++i) {
        present = present || core[i] == premise;
      }
      ASS(present);
    }
  }
}

}

TEST_FUN(empty_and_reset)
{
  SimpleCongruenceClosure actual(nullptr);
  for (unsigned round = 0; round < 3; ++round) {
    ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
    ASS_EQ(actual.getUnsatCoreCount(), 0u);
    actual.reset();
  }
}

TEST_FUN(equivalence_and_congruence_matrix)
{
  Fixture fixture;
  SimpleCongruenceClosure actual(nullptr);
  for (unsigned mask = 0; mask < 256; ++mask) {
    auto inputs = fixture.inputs(mask);
    Relation expected(fixture.nodes, inputs);
    for (bool reverse : {false, true}) {
      actual.reset();
      if (reverse) { std::reverse(inputs.begin(), inputs.end()); }
      add(actual, inputs);
      ASS_REP2(actual.getStatus(mask % 2) == DecisionProcedure::SATISFIABLE, mask, reverse);
      ASS_REP2(actual.getUnsatCoreCount() == 0u, mask, reverse);
      for (unsigned left = 0; left < fixture.terms.size(); ++left) {
        for (unsigned right = 0; right < fixture.terms.size(); ++right) {
          Context context{mask, left, right, reverse};
          bool same = actual.getClassID(fixture.terms[left]) == actual.getClassID(fixture.terms[right]);
          ASS_REP(same == expected.same(left, right), context);
        }
      }
    }
  }
}

TEST_FUN(disequality_and_core_matrix)
{
  Fixture fixture;
  SimpleCongruenceClosure actual(nullptr);
  const std::array<std::pair<unsigned, unsigned>, 4> queries{{{0, 3}, {4, 6}, {9, 10}, {11, 12}}};
  for (unsigned mask = 0; mask < 256; ++mask) {
    for (auto query : queries) {
      auto inputs = fixture.inputs(mask);
      inputs.push_back(fixture.equality(query.first, query.second, false));
      Relation expected(fixture.nodes, inputs);
      bool unsat = expected.inconsistent(inputs);
      Context context{mask, query.first, query.second, false};
      actual.reset();
      add(actual, inputs);
      auto status = actual.getStatus(mask % 2);
      ASS_REP(status == (unsat ? DecisionProcedure::UNSATISFIABLE
                              : DecisionProcedure::SATISFIABLE), context);
      if (unsat) {
        verifyCores(actual, fixture, inputs, context);
      } else {
        ASS_REP(actual.getUnsatCoreCount() == 0u, context);
      }
    }
  }
}

TEST_FUN(multiple_independent_cores_and_reset)
{
  Fixture fixture;
  SimpleCongruenceClosure actual(nullptr);
  auto inputs = fixture.inputs(0);
  for (auto pair : {std::pair<unsigned, unsigned>{0, 1}, {2, 3}}) {
    inputs.push_back(fixture.equality(pair.first, pair.second));
    inputs.push_back(fixture.equality(pair.first, pair.second, false));
  }
  add(actual, inputs);
  ASS_EQ(actual.getStatus(true), DecisionProcedure::UNSATISFIABLE);
  ASS_EQ(actual.getUnsatCoreCount(), 2u);
  verifyCores(actual, fixture, inputs);
  actual.reset();
  auto clean = fixture.inputs(0);
  clean.push_back(fixture.equality(0, 1, false));
  add(actual, clean);
  ASS_EQ(actual.getStatus(true), DecisionProcedure::SATISFIABLE);
  ASS_EQ(actual.getUnsatCoreCount(), 0u);
}

TEST_FUN(predicate_congruence_and_complementary_atoms)
{
  DECL_SORT(predicate_sort)
  DECL_CONST(a, predicate_sort)
  DECL_CONST(b, predicate_sort)
  DECL_PRED(p, {predicate_sort})
  DECL_PRED(proposition, {})
  SimpleCongruenceClosure actual(nullptr);
  Literal* positive = p(a);
  Literal* negative = ~p(b);
  Literal* equality = (a == b);

  // A two-element model separates a and b and assigns p opposite values.
  actual.addLiteral(positive);
  actual.addLiteral(negative);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
  ASS_NEQ(actual.getClassID(a), actual.getClassID(b));
  actual.reset();
  for (Literal* premise : {positive, negative, equality}) {
    actual.addLiteral(premise);
  }
  ASS_EQ(actual.getStatus(false), DecisionProcedure::UNSATISFIABLE);
  verifyNecessaryPremises(actual, {positive, negative, equality});

  actual.reset();
  Literal* prop = proposition();
  Literal* notProp = ~proposition();
  actual.addLiteral(prop);
  actual.addLiteral(notProp);
  ASS_EQ(actual.getStatus(true), DecisionProcedure::UNSATISFIABLE);
  verifyNecessaryPremises(actual, {prop, notProp});
}

TEST_FUN(variables_are_constants_in_fine_grained_insertion)
{
  DECL_SORT(variable_sort)
  DECL_VAR_SORTED(x, 0, variable_sort)
  DECL_VAR_SORTED(y, 1, variable_sort)
  DECL_FUNC(f, {variable_sort}, variable_sort)
  SimpleCongruenceClosure actual(nullptr);
  // addLiteral explicitly treats variables as constants, not as universally
  // quantified variables. A two-element model with f the identity suffices.
  actual.addLiteral(x != y);
  actual.addLiteral(f(x) != f(y));
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
  ASS_NEQ(actual.getClassID(x), actual.getClassID(y));
  actual.reset();
  Literal* same = (x == y);
  Literal* differentImages = (f(x) != f(y));
  actual.addLiteral(same);
  actual.addLiteral(differentImages);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::UNSATISFIABLE);
  verifyNecessaryPremises(actual, {same, differentImages});

  // EUF permits a fixed point. No free-constructor or occurs-check rule applies.
  actual.reset();
  actual.addLiteral(x == f(x));
  actual.addLiteral(x != y);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
  ASS_EQ(actual.getClassID(x), actual.getClassID(f(x)));
  actual.reset();
  Literal* reflexiveDisequality = (x != x);
  actual.addLiteral(reflexiveDisequality);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::UNSATISFIABLE);
  verifyNecessaryPremises(actual, {reflexiveDisequality});
}

TEST_FUN(internal_distinct_marker_contract)
{
  DECL_SORT(distinct_sort)
  DECL_CONST(a, distinct_sort)
  DECL_CONST(b, distinct_sort)
  DECL_CONST(c, distinct_sort)
  // These are direct API checks. DistinctGroupExpansion removes the marker
  // before the solver normally calls this decision procedure.
  PredSugar distinct(env.signature->getDistinctPredicate(3, a.sort()));
  Literal* allDifferent = distinct(a, b, c);
  Literal* someEqual = ~distinct(a, b, c);
  Literal* equality = (a == b);
  SimpleCongruenceClosure actual(nullptr);
  actual.addLiteral(allDifferent);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
  actual.reset();
  actual.addLiteral(allDifferent);
  actual.addLiteral(equality);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::UNSATISFIABLE);
  verifyNecessaryPremises(actual, {allDifferent, equality});

  actual.reset();
  actual.addLiteral(someEqual);
  // The negative-marker path is incomplete. A one-element model witnesses
  // satisfiability, but UNKNOWN is an allowed decision-procedure result.
  auto status = actual.getStatus(false);
  ASS(status == DecisionProcedure::SATISFIABLE || status == DecisionProcedure::UNKNOWN);
  ASS_EQ(actual.getUnsatCoreCount(), 0u);
  actual.reset();
  actual.addLiteral(someEqual);
  actual.addLiteral(equality);
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
  ASS_EQ(actual.getUnsatCoreCount(), 0u);
}
