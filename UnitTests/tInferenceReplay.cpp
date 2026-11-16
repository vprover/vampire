/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Options.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Parse/TPTP.hpp"
#include <sstream>

using namespace Kernel;
using namespace Test;
using Shell::InferenceRecorder;

TEST_FUN(replay_preserves_environment_and_parent_state)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_PRED(p, {s})
  auto left = clause({selected(p(x)), p(a)});
  auto goal = clause({p(a)}, GeneratingInference1(InferenceRule::FACTORING, left));
  left->setAge(17);
  auto leftStore = left->store();
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.setMainProblem(&problem);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("saturation_algorithm", "lrs");
  env.reconstruction = false;
  auto ordering = OrderingSP(Ordering::create(problem, *env.options));
  auto savedOrdering = OrderingSP(Ordering::create(problem, *env.options));
  InferenceStore::instance()->ordering = savedOrdering;
  {
    Shell::InferenceReplayer replayer;
    replayer.makeInferenceEngine(ordering);
    ASS(!env.reconstruction);
    ASS_EQ(env.options->saturationAlgorithm(), Shell::Options::SaturationAlgorithm::LRS);
    ASS_EQ(&Saturation::SaturationAlgorithm::tryGetInstance()->getOrdering(), ordering.ptr());
    ASS_EQ(InferenceStore::instance()->ordering.ptr(), savedOrdering.ptr());
    for (unsigned i = 0; i < 2; ++i) {
      replayer.replayInference(goal);
      auto info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
      ASS(info);
      auto factoring = std::get_if<InferenceRecorder::FactoringInformation>(&info->details);
      ASS(factoring);
      ASS_EQ(factoring->removedLiteral.premiseIndex, 0);
      ASS_L(factoring->removedLiteral.literalIndex, left->length());
      ASS_EQ(info->substitutionForBanksSub.size(), 1);
      ASS_EQ(info->substitutionForBanksSub[0].apply(0), TermList(a));
      ASS_EQ(env.getMainProblem(), &problem);
      ASS(env.initiallyHasNonDefaultSorts());
      ASS(!env.reconstruction);
      ASS_EQ(left->store(), leftStore);
      ASS_EQ(left->age(), 17);
    }
  }
  ASS_EQ(env.getMainProblem(), &problem);
  ASS(!env.reconstruction);
  ASS_EQ(InferenceStore::instance()->ordering.ptr(), savedOrdering.ptr());
}

TEST_FUN(constrained_resolution_records_substitutions_and_constraints)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto left = clause({selected(p(f(x))), q(x)});
  auto right = clause({selected(~p(g(y))), r(y)});
  TermList u = TermList::var(8), v = TermList::var(9);
  auto goal = clause({q(u), f(u) != g(v), r(v)},
      GeneratingInference2(InferenceRule::CONSTRAINED_RESOLUTION, left, right));
  Problem problem;
  auto units = UnitList::singleton(goal);
  UnitList::push(left, units);
  UnitList::push(right, units);
  problem.addUnits(units);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  auto oldUwa = env.options->unificationWithAbstraction();
  env.options->setUWA(Shell::Options::UnificationWithAbstraction::ALL);
  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  replayer.replayInference(goal);
  auto info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
  ASS(info);
  auto resolution = std::get_if<InferenceRecorder::ResolutionInformation>(&info->details);
  ASS(resolution);
  ASS_EQ(resolution->constraints.literals.size(), 1);
  ASS_EQ(resolution->constraints.literals[0], (*goal)[1]);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), u);
  ASS_EQ(info->substitutionForBanksSub[1].apply(1), v);
  ASS_EQ(resolution->resolvedLiterals.left.premiseIndex, 0);
  ASS_EQ(resolution->resolvedLiterals.left.literalIndex, 0);
  ASS_EQ(resolution->resolvedLiterals.right.premiseIndex, 1);
  ASS_EQ(resolution->resolvedLiterals.right.literalIndex, 0);
  env.options->setUWA(oldUwa);
}

static void replayRewriteWithIndependentParentBanks(InferenceRule rule)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  auto main = clause({selected(p(f(x)))});
  auto equality = clause({selected(f(y) == y)});
  TermList renamed = TermList::var(9);
  auto goal = rule == InferenceRule::SUPERPOSITION
      ? clause({p(renamed)}, GeneratingInference2(rule, main, equality))
      : clause({p(renamed)}, SimplifyingInference2(rule, main, equality));
  Problem problem;
  auto units = UnitList::singleton(goal);
  UnitList::push(main, units);
  UnitList::push(equality, units);
  problem.addUnits(units);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  replayer.replayInference(goal);
  auto info = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
  ASS(info);
  ASS_EQ(info->substitutionForBanksSub.size(), 2);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
  ASS_EQ(info->substitutionForBanksSub[1].apply(1), renamed);
  const InferenceRecorder::RewriteInformation* rewrite;
  if (rule == InferenceRule::SUPERPOSITION) {
    auto details = std::get_if<InferenceRecorder::SuperpositionInformation>(&info->details);
    ASS(details);
    ASS(details->constraints.literals.empty());
    rewrite = &details->rewrite;
  } else {
    auto details = std::get_if<InferenceRecorder::ForwardDemodulationInformation>(&info->details);
    ASS(details);
    rewrite = &details->rewrite;
  }
  ASS_EQ(rewrite->rewrittenLiteral.premiseIndex, 0);
  ASS_EQ(rewrite->equality.premiseIndex, 1);
  ASS_EQ(rewrite->from, TermList(f(renamed)));
  ASS_EQ(rewrite->to, renamed);
}

TEST_FUN(superposition_applicators_preserve_parent_banks)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::SUPERPOSITION);
}

TEST_FUN(demodulation_applicators_preserve_original_variable_names)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::FORWARD_DEMODULATION);
}

TEST_FUN(tptp_replay_flag_prints_substitutions_only_when_enabled)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto left = clause({selected(~p(x)), q(x)});
  auto right = clause({selected(p(a))});
  auto goal = clause({q(a)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  Problem problem;
  auto units = UnitList::singleton(goal);
  UnitList::push(left, units);
  UnitList::push(right, units);
  problem.addUnits(units);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->setProof(Shell::Options::Proof::TPTP);
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  ASS(!env.options->replay());
  std::ostringstream disabled;
  store->outputProof(disabled, goal);
  ASS(disabled.str().find("unifier(") == std::string::npos);
  env.options->set("replay", "on");
  std::ostringstream enabled;
  store->outputProof(enabled, goal);
  auto proof = enabled.str();
  ASS(proof.find("unifier([subs(f" + std::to_string(left->number()) + ",[b(X0,a)])") != std::string::npos);
  ASS(proof.find("[,unifier") == std::string::npos);
  std::istringstream input(proof);
  Parse::TPTP parser(input, "replayed-proof.p");
  parser.parse();
  env.options->set("replay", "off");
  std::ostringstream disabledAgain;
  store->outputProof(disabledAgain, goal);
  ASS_EQ(disabledAgain.str(), disabled.str());
}

TEST_FUN(alpha_matching_preserves_duplicate_counts_and_rejects_variable_merging)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto parent = clause({p(x), p(y), q(x)});
  TermList renamed = TermList::var(9);
  auto goal = clause({q(renamed), p(renamed), p(renamed)},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  auto wrongCounts = clause({p(x), q(x), q(x)},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  auto merging = clause({p(x), p(y), q(x)},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  auto correct = clause({p(x), p(x), q(x)},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  IdentityApplicator identity;
  auto recorder = InferenceRecorder::instance();
  recorder->setCurrentGoal(goal);
  recorder->factoring(wrongCounts, parent, {&identity}, (*parent)[0]);
  ASS(!recorder->getLastRecordedInferenceInformation());
  recorder->factoring(merging, parent, {&identity}, (*parent)[0]);
  ASS(!recorder->getLastRecordedInferenceInformation());
  recorder->factoring(correct, parent, {&identity}, (*parent)[0]);
  auto info = recorder->getLastRecordedInferenceInformation();
  ASS(info);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
}

TEST_FUN(alpha_matching_accepts_reversed_equalities)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto parent = clause({p(x), p(y)});
  TermList renamed = TermList::var(9);
  auto goal = clause({a == renamed, p(renamed)},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  auto candidate = clause({p(x), x == a},
      GeneratingInference1(InferenceRule::FACTORING, parent));
  IdentityApplicator identity;
  auto recorder = InferenceRecorder::instance();
  recorder->setCurrentGoal(goal);
  recorder->factoring(candidate, parent, {&identity}, (*parent)[0]);
  auto info = recorder->getLastRecordedInferenceInformation();
  ASS(info);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
}
