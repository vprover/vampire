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
#include "Shell/InferenceReplay.hpp"

#include <vector>

using namespace Test;

static void checkStep(Clause *conclusion)
{
  Problem problem;
  UnitList* units = nullptr;
  auto parents = conclusion->getParents();
  while (parents.hasNext()) { UnitList::push(parents.next(), units); }
  problem.addUnits(units);
  env.setMainProblem(&problem);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  std::ostringstream out;
  Shell::SMTCheck::outputSignature(out);
  Shell::SMTCheck::outputStep(out, conclusion, &replayer);
  z3::context context;
  std::string result = Z3_eval_smtlib2_string(context, out.str().c_str());
  context.check_error();
  ASS_EQ(result, "unsat\n");
}

static std::vector<Clause*> generatedConclusions;

class SMTGenerationTester : public Generation::GenerationTester {
public:
  bool eq(Clause *result, Clause *expected) override
  {
    generatedConclusions.push_back(result);
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

  generatedConclusions.clear();
  Generation::SymmetricTest()
    .inputs({clause({selected(p(x)), selected(q(y))}),
             clause({selected(~p(x)), r(x)})})
    .options({{"proof_extra", "full"}, {"literal_maximality_aftercheck", aftercheck},
              {"selection", selection}})
    .expected(exactly(clause({q(y), r(x)})))
    .run<Inferences::BinaryResolution, SMTGenerationTester>();
  // The generation tester's saturation engine must be released before replay
  // creates its own engine (Vampire permits only one at a time).
  for (Clause* conclusion : generatedConclusions) { checkStep(conclusion); }
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
  auto left = clause({selected(Lit(positive)), q(y)});
  auto right = clause({selected(Lit(negative))});
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
  auto left = clause({selected(Lit(positive)), q(x,y)});
  auto right = clause({selected(Lit(negative)), r(z)});
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
  auto left = clause({selected(Lit(positive))}), right = clause({selected(Lit(negative))});
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
  Literal *resolved = p(x), *other = p(y);
  auto premise = clause({selected(Lit(resolved)), other, q(z)});
  auto conclusion = clause({q(x), p(y)}, GeneratingInference1(InferenceRule::FACTORING, premise));
  env.proofExtra.insert(conclusion, new Inferences::FactoringExtra(resolved, other));
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
  Literal *resolved = f(x) != f(y);
  auto premise = clause({selected(Lit(resolved)), q(z), r(x)});
  auto conclusion = clause({q(y), r(x)}, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, premise));
  env.proofExtra.insert(conclusion, new Inferences::EqualityResolutionExtra(resolved));
  checkStep(conclusion);
}

TEST_FUN(resolution_duplicate_literals)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s})
  Literal *positive = p(x), *negative = ~p(y);
  auto left = clause({selected(Lit(positive)), q(x)}), right = clause({selected(Lit(negative)), q(y)});
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
  auto left = clause({selected(Lit(positive)), q(x,x), q(x,f(x))}), right = clause({selected(Lit(negative))});
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
  auto left = clause({selected(Lit(positive)), f(x) == y}), right = clause({selected(Lit(negative))});
  auto conclusion = clause({x == f(z)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  env.proofExtra.insert(conclusion, new Inferences::BinaryResolutionExtra(positive, negative));
  checkStep(conclusion);
}

TEST_FUN(forward_demodulation_instantiates_the_side_bank)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(p, {s})
  auto main = clause({p(f(a))});
  auto side = clause({f(x) == x});
  auto conclusion = clause({p(a)}, SimplifyingInference2(InferenceRule::FORWARD_DEMODULATION, main, side));
  checkStep(conclusion);
}

TEST_FUN(backward_demodulation_instantiates_the_side_bank)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(p, {s})
  auto main = clause({p(f(a))});
  auto side = clause({f(x) == x});
  auto conclusion = clause({p(a)}, SimplifyingInference2(InferenceRule::BACKWARD_DEMODULATION, main, side));
  checkStep(conclusion);
}

TEST_FUN(forward_demodulation_translates_both_banks_to_conclusion_names)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_FUNC(f, {s}, s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s})
  auto main = clause({p(f(x)), q(x)});
  auto side = clause({f(x) == x});
  TermList v = TermList::var(9);
  auto conclusion = clause({p(v), q(v)}, SimplifyingInference2(InferenceRule::FORWARD_DEMODULATION, main, side));
  checkStep(conclusion);
}

TEST_FUN(missing_replayer_reports_an_unchecked_step)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_PRED(p, {s})
  auto left = clause({selected(p(x))});
  auto right = clause({selected(~p(x))});
  auto conclusion = clause(Stack<Lit>(), GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  std::ostringstream out;
  Shell::SMTCheck::outputStep(out, conclusion);
  ASS(out.str().find("sorry: could not replay resolution") != std::string::npos);
  ASS(out.str().find("(check-sat)") == std::string::npos);
}
