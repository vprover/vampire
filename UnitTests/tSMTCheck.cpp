/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <sstream>
#include <z3++.h>

#include "Test/GenerationTester.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Shell/SMTCheck.hpp"

using namespace Test;

static void checkStep(Clause *conclusion)
{
  std::ostringstream out;
  Shell::SMTCheck::outputSignature(out);
  Shell::SMTCheck::outputStep(out, conclusion);
  z3::context context;
  std::string result = Z3_eval_smtlib2_string(context, out.str().c_str());
  context.check_error();
  ASS_EQ(result, "unsat\n");
}

class SMTGenerationTester : public Generation::GenerationTester {
public:
  bool eq(Clause *result, Clause *expected) override
  {
    checkStep(result);
    return Generation::GenerationTester::eq(result, expected);
  }
};

static void checkResolution(const char *aftercheck, const char *selection)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_SORT(t)
  DECL_PRED(p, {s})
  DECL_PRED(q, {t})
  DECL_PRED(r, {s})

  Generation::SymmetricTest()
    .inputs({clause({selected(p(x)), selected(q(y))}),
             clause({selected(~p(x)), r(x)})})
    .options({{"proof_extra", "full"}, {"literal_maximality_aftercheck", aftercheck},
              {"selection", selection}})
    .expected(exactly(clause({q(y), r(x)})))
    .run<Inferences::BinaryResolution, SMTGenerationTester>();
}

TEST_FUN(resolution_aftercheck) { checkResolution("on", "1"); }
TEST_FUN(resolution_without_aftercheck) { checkResolution("off", "1"); }
TEST_FUN(resolution_incomplete_selection) { checkResolution("on", "0"); }

TEST_FUN(resolution_eliminated_variable)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_SORT(t)
  DECL_PRED(p, {s})
  DECL_PRED(q, {t})
  Literal *positive = p(x), *negative = ~p(x);
  auto left = clause({positive, q(y)});
  auto right = clause({negative});
  auto conclusion = clause({q(y)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(resolution_reordered_conclusion)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_SORT(t)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s, t})
  DECL_PRED(r, {t})
  Literal *positive = p(x), *negative = ~p(x);
  auto left = clause({positive, q(x,y)});
  auto right = clause({negative, r(z)});
  auto conclusion = clause({r(x), q(z,y)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(resolution_empty_conclusion)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_PRED(p, {s})
  Literal *positive = p(x), *negative = ~p(x);
  auto left = clause({positive}), right = clause({negative});
  auto conclusion = clause(Stack<Lit>(), GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(factoring_renamed_conclusion)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_SORT(t)
  DECL_PRED(p, {s})
  DECL_PRED(q, {t})
  Literal *selected = p(x), *other = p(y);
  auto premise = clause({selected, other, q(z)});
  auto conclusion = clause({q(x), p(y)}, GeneratingInference1(InferenceRule::FACTORING, premise));
  env.proofExtra.insert(conclusion, new Inferences::FactoringExtra(selected, other));
  checkStep(conclusion);
}

TEST_FUN(equality_resolution_renamed_conclusion)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_SORT(t)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(q, {t})
  DECL_PRED(r, {s})
  Literal *selected = f(x) != f(y);
  auto premise = clause({selected, q(z), r(x)});
  auto conclusion = clause({q(y), r(x)}, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, premise));
  env.proofExtra.insert(conclusion, new Inferences::EqualityResolutionExtra(selected));
  checkStep(conclusion);
}

TEST_FUN(resolution_duplicate_literals)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s})
  Literal *positive = p(x), *negative = ~p(y);
  auto left = clause({positive, q(x)}), right = clause({negative, q(y)});
  auto conclusion = clause({q(z), q(z)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(resolution_multiple_candidates)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s, s})
  Literal *positive = p(x), *negative = ~p(x);
  auto left = clause({positive, q(x,x), q(x,f(x))}), right = clause({negative});
  auto conclusion = clause({q(z,f(z)), q(z,z)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(resolution_equality_arguments)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(p, {s})
  Literal *positive = p(x), *negative = ~p(x);
  auto left = clause({positive, f(x) == y}), right = clause({negative});
  auto conclusion = clause({x == f(z)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}
