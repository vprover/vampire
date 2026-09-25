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
#include "Kernel/LPO.hpp"
#include "Kernel/SortHelper.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <iostream>
#include <memory>
#include <numeric>
#include <string>
#include <utility>
#include <vector>

using namespace DP;
using namespace Kernel;
using namespace Lib;

namespace {

// Ground syntax trees used only by the reference checks. Rewriting below does
// not call Vampire's matcher, rewriter, class-ID API or congruence procedure.
struct Tree {
  unsigned symbol;
  std::vector<Tree> arguments;
  bool operator==(const Tree&) const = default;
};

std::ostream& operator<<(std::ostream& out, const Tree& tree)
{
  out << tree.symbol << '(';
  for (const auto& argument : tree.arguments) {
    out << argument << ',';
  }
  return out << ')';
}

Tree tree(TermList term)
{
  ASS(term.isTerm());
  ASS(term.term()->ground());
  Tree result{term.term()->functor(), {}};
  for (unsigned i = 0; i < term.term()->arity(); ++i) {
    result.arguments.push_back(tree(*term.term()->nthArgument(i)));
  }
  return result;
}

struct Rule { Tree left; Tree right; };
using Equations = std::vector<std::pair<TermList, TermList>>;

Tree normalize(Tree value, const std::vector<Rule>& rules,
               unsigned& remaining, int omitted = -1)
{
  for (auto& argument : value.arguments) {
    argument = normalize(argument, rules, remaining, omitted);
  }
  for (unsigned i = 0; i < rules.size(); ++i) {
    if (static_cast<int>(i) != omitted && value == rules[i].left) {
      ASS_REP(remaining > 0, value);
      --remaining;
      return normalize(rules[i].right, rules, remaining, omitted);
    }
  }
  return value;
}

Tree normalForm(Tree value, const std::vector<Rule>& rules, int omitted = -1)
{
  // Every accepted rule decreases the supplied LPO. The budget also keeps a
  // broken model from making the reference checker run without a bound.
  unsigned remaining = 4096;
  return normalize(std::move(value), rules, remaining, omitted);
}

unsigned include(std::vector<Tree>& universe, const Tree& value)
{
  for (const auto& argument : value.arguments) {
    include(universe, argument);
  }
  auto found = std::find(universe.begin(), universe.end(), value);
  if (found != universe.end()) {
    return static_cast<unsigned>(found - universe.begin());
  }
  universe.push_back(value);
  return static_cast<unsigned>(universe.size() - 1);
}

// A subterm-closed finite congruence relation: reflexivity, input equations,
// transitive closure and the defining congruence property. No union-find,
// ordering, term orientation or production model extraction is used here.
class Relation {
public:
  Relation(const std::vector<Tree>& universe, const Equations& equations)
    : _same(universe.size(), std::vector<bool>(universe.size(), false))
  {
    auto index = [&](const Tree& value) {
      auto found = std::find(universe.begin(), universe.end(), value);
      ASS(found != universe.end());
      return static_cast<unsigned>(found - universe.begin());
    };
    std::vector<std::vector<unsigned>> arguments;
    for (unsigned i = 0; i < universe.size(); ++i) {
      _same[i][i] = true;
      arguments.emplace_back();
      for (const auto& argument : universe[i].arguments) {
        arguments.back().push_back(index(argument));
      }
    }
    for (const auto& equation : equations) {
      unsigned left = index(tree(equation.first));
      unsigned right = index(tree(equation.second));
      _same[left][right] = _same[right][left] = true;
    }
    bool changed;
    do {
      changed = false;
      for (unsigned middle = 0; middle < universe.size(); ++middle) {
        for (unsigned left = 0; left < universe.size(); ++left) {
          for (unsigned right = 0; right < universe.size(); ++right) {
            if (!_same[left][right] && _same[left][middle] && _same[middle][right]) {
              _same[left][right] = true;
              changed = true;
            }
          }
        }
      }
      for (unsigned left = 0; left < universe.size(); ++left) {
        for (unsigned right = 0; right < left; ++right) {
          if (_same[left][right] || universe[left].symbol != universe[right].symbol ||
              arguments[left].size() != arguments[right].size()) {
            continue;
          }
          bool sameArguments = true;
          for (unsigned i = 0; i < arguments[left].size(); ++i) {
            sameArguments = sameArguments && _same[arguments[left][i]][arguments[right][i]];
          }
          if (sameArguments) {
            _same[left][right] = _same[right][left] = true;
            changed = true;
          }
        }
      }
    } while (changed);
  }

  bool same(unsigned left, unsigned right) const { return _same[left][right]; }

private:
  std::vector<std::vector<bool>> _same;
};

struct Fixture {
  TermList sort;
  std::vector<TermList> terms;

  Fixture()
  {
    DECL_SORT(modelSort)
    DECL_CONST(a, modelSort)
    DECL_CONST(b, modelSort)
    DECL_CONST(c, modelSort)
    DECL_CONST(d, modelSort)
    DECL_FUNC(f, {modelSort}, modelSort)
    DECL_FUNC(g, {modelSort}, modelSort)
    DECL_FUNC(h, {modelSort, modelSort}, modelSort)
    sort = a.sort();
    const std::vector<TermSugar> expressions{
      a, b, c, d, f(a), f(b), f(c), g(a), g(b),
      h(a,b), h(b,a), h(a,a), f(f(a)), f(f(b)),
      g(f(a)), g(f(b)), h(f(a),g(b)), h(f(b),g(a))
    };
    for (const auto& expression : expressions) {
      terms.push_back(expression.sugaredExpr());
    }
  }

  Equations equations(std::initializer_list<std::pair<unsigned, unsigned>> indices) const
  {
    Equations result;
    for (const auto& [left, right] : indices) {
      result.emplace_back(terms.at(left), terms.at(right));
    }
    return result;
  }
};

LPO ordering(bool reverse = false)
{
  auto functions = DArray<int>::fromIterator(getRangeIterator(0, static_cast<int>(env.signature->functions())));
  if (reverse) {
    for (unsigned i = 0; i < functions.size(); ++i) {
      functions[i] = static_cast<int>(functions.size() - 1 - i);
    }
  }
  return LPO(std::move(functions),
             DArray<int>::fromIterator(getRangeIterator(0, static_cast<int>(env.signature->typeCons()))),
             DArray<int>::fromIterator(getRangeIterator(0, static_cast<int>(env.signature->predicates()))),
             PrecedenceOrdering::testLevels(), false);
}

void load(SimpleCongruenceClosure& actual, const Fixture& fixture,
          const Equations& equations, const std::vector<TermList>& probes, bool reverse = false)
{
  // Reflexive equalities register the probe terms without changing the theory.
  // Only positive ground equalities enter this model-extraction instance.
  for (unsigned i = 0; i < probes.size(); ++i) {
    TermList term = probes[reverse ? probes.size() - 1 - i : i];
    actual.addLiteral(Literal::createEquality(true, term, term, fixture.sort));
  }
  for (const auto& [left, right] : equations) {
    std::cout << "input " << left.toString() << " = " << right.toString() << std::endl;
    actual.addLiteral(Literal::createEquality(true, left, right, fixture.sort));
  }
  ASS_EQ(actual.getStatus(false), DecisionProcedure::SATISFIABLE);
}

void verify(SimpleCongruenceClosure& actual, const Ordering& ord, const Fixture& fixture,
            const Equations& equations, const std::vector<TermList>& probes)
{
  LiteralStack model;
  std::cout << "extract model" << std::endl;
  actual.getModel(model);
  std::vector<Rule> rules;
  std::vector<Tree> universe;
  for (TermList term : probes) {
    include(universe, tree(term));
  }
  for (const auto& [left, right] : equations) {
    include(universe, tree(left));
    include(universe, tree(right));
  }
  for (unsigned i = 0; i < model.size(); ++i) {
    Literal* literal = model[i];
    std::cout << "model " << literal->toString() << std::endl;
    ASS(literal->isEquality() && literal->isPositive() && literal->ground());
    ASS_EQ(SortHelper::getEqualityArgumentSort(literal), fixture.sort);
    TermList left = *literal->nthArgument(0);
    TermList right = *literal->nthArgument(1);
    auto comparison = ord.compare(left, right);
    ASS_REP2(comparison == Ordering::Result::GREATER || comparison == Ordering::Result::LESS,
             left.toString(), right.toString());
    // Shared equality literals may canonicalize their argument order. Orient
    // them using the caller's ordering, not the literal's storage positions.
    if (comparison == Ordering::Result::LESS) {
      std::swap(left, right);
    }
    Rule rule{tree(left), tree(right)};
    include(universe, rule.left);
    include(universe, rule.right);
    for (const auto& previous : rules) {
      ASS_REP(!(previous.left == rule.left), rule.left);
    }
    rules.push_back(std::move(rule));
  }
  for (unsigned i = 0; i < rules.size(); ++i) {
    ASS_REP2(normalForm(rules[i].right, rules) == rules[i].right, rules[i].left, rules[i].right);
    ASS_REP(normalForm(rules[i].left, rules, static_cast<int>(i)) == rules[i].left, rules[i].left);
    for (const auto& argument : rules[i].left.arguments) {
      ASS_REP(normalForm(argument, rules) == argument, rules[i].left);
    }
  }
  Relation expected(universe, equations);
  std::vector<Tree> normalized;
  for (const auto& term : universe) {
    normalized.push_back(normalForm(term, rules));
  }
  for (unsigned left = 0; left < universe.size(); ++left) {
    for (unsigned right = 0; right < universe.size(); ++right) {
      ASS_REP2((normalized[left] == normalized[right]) == expected.same(left, right),
               universe[left], universe[right]);
    }
  }
}

void single(std::initializer_list<std::pair<unsigned, unsigned>> indices)
{
  Fixture fixture;
  auto ord = ordering();
  SimpleCongruenceClosure actual(&ord);
  auto equations = fixture.equations(indices);
  load(actual, fixture, equations, fixture.terms);
  verify(actual, ord, fixture, equations, fixture.terms);
}

}

TEST_FUN(empty_reflexive_and_reset)
{
  Fixture fixture;
  auto ord = ordering();
  SimpleCongruenceClosure actual(&ord);
  load(actual, fixture, {}, {});
  verify(actual, ord, fixture, {}, {});
  actual.reset();
  load(actual, fixture, {}, fixture.terms);
  verify(actual, ord, fixture, {}, fixture.terms);
}

TEST_FUN(constant_chain) { single({{0,1}, {1,2}, {2,3}}); }
TEST_FUN(unary_congruence) { single({{0,1}, {4,2}, {7,3}}); }
TEST_FUN(binary_argument_positions) { single({{0,1}, {9,2}, {11,3}}); }
TEST_FUN(collapsing_ground_equations) { single({{4,0}, {7,1}, {9,0}}); }

TEST_FUN(sixty_four_equation_subsets)
{
  Fixture fixture;
  auto ord = ordering();
  SimpleCongruenceClosure actual(&ord);
  const std::vector<std::pair<unsigned, unsigned>> choices{{0,1}, {1,2}, {4,7}, {9,10}, {4,0}, {7,3}};
  for (unsigned mask = 0; mask < (1U << choices.size()); ++mask) {
    actual.reset();
    Equations equations;
    for (unsigned bit = 0; bit < choices.size(); ++bit) {
      if (mask & (1U << bit)) {
        auto [left, right] = choices[bit];
        equations.emplace_back(fixture.terms[left], fixture.terms[right]);
      }
    }
    std::cout << "equation mask " << mask << std::endl;
    load(actual, fixture, equations, fixture.terms, (mask & 1) != 0);
    verify(actual, ord, fixture, equations, fixture.terms);
  }
}

TEST_FUN(repeated_model_extraction)
{
  Fixture fixture;
  auto ord = ordering();
  SimpleCongruenceClosure actual(&ord);
  auto equations = fixture.equations({{0,1}, {4,2}, {9,3}});
  load(actual, fixture, equations, fixture.terms);
  for (unsigned repeat = 0; repeat < 4; ++repeat) {
    verify(actual, ord, fixture, equations, fixture.terms);
  }
}

TEST_FUN(reset_replaces_equations)
{
  Fixture fixture;
  auto ord = ordering();
  SimpleCongruenceClosure actual(&ord);
  const std::vector<Equations> rounds{
    fixture.equations({{0,1}, {1,2}}), {}, fixture.equations({{0,3}, {4,7}}), {}
  };
  for (const auto& equations : rounds) {
    actual.reset();
    load(actual, fixture, equations, fixture.terms);
    verify(actual, ord, fixture, equations, fixture.terms);
  }
}





TEST_FUN(sequential_instances)
{
  Fixture fixture;
  auto ord = ordering();
  {
    SimpleCongruenceClosure first(&ord);
    auto equations = fixture.equations({{0,1}});
    std::vector<TermList> probes{fixture.terms[0], fixture.terms[1]};
    load(first, fixture, equations, probes);
    verify(first, ord, fixture, equations, probes);
  }
  SimpleCongruenceClosure second(&ord);
  auto equations = fixture.equations({{1,2}, {4,7}, {9,3}});
  load(second, fixture, equations, fixture.terms, true);
  verify(second, ord, fixture, equations, fixture.terms);
}
