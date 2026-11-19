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
#include "Inferences/Superposition.hpp"
#include "Shell/Options.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Parse/TPTP.hpp"
#include <sstream>

using namespace Kernel;
using namespace Test;
using Shell::InferenceRecorder;
using Inferences::InferenceReplayInformation;

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
  env.replayRecording = false;
  auto ordering = OrderingSP(Ordering::create(problem, *env.options));
  auto savedOrdering = OrderingSP(Ordering::create(problem, *env.options));
  InferenceStore::instance()->ordering = savedOrdering;
  {
    Shell::InferenceReplayer replayer;
    replayer.makeInferenceEngine(ordering);
    ASS(!env.replayRecording);
    ASS_EQ(env.options->saturationAlgorithm(), Shell::Options::SaturationAlgorithm::LRS);
    ASS_EQ(&Saturation::SaturationAlgorithm::tryGetInstance()->getOrdering(), ordering.ptr());
    ASS_EQ(InferenceStore::instance()->ordering.ptr(), savedOrdering.ptr());
    for (unsigned i = 0; i < 2; ++i) {
      auto info = replayer.replayInference(goal);
      ASS(info);
      ASS_EQ(env.proofExtra.find(goal)->findComponent<Inferences::InferenceReplayInformation>(), info);
      ASS_EQ(info->conclusion, goal);
      ASS_EQ(&env.proofExtra.get<InferenceReplayInformation>(goal), info);
      ASS(!env.proofExtra.find(goal)->findComponent<Inferences::RewriteInferenceExtra>());
      const auto& extra = env.proofExtra.get<Inferences::TwoLiteralInferenceExtra>(goal);
      ASS_EQ(extra.get<Inferences::LiteralInferenceExtra>().literal(), (*left)[0]);
      ASS_EQ(extra.get<Inferences::OtherLiteralInferenceExtra>().literal(), (*left)[1]);
      const auto& kept = extra.get<Inferences::LiteralInferenceExtra>().position;
      const auto& removed = extra.get<Inferences::OtherLiteralInferenceExtra>().position;
      ASS(kept);
      ASS(removed);
      ASS_EQ(*kept, 0);
      ASS_EQ(*removed, 1);
      ASS_EQ(info->premises.size(), 1);
      ASS_EQ(info->substitutionForBanksSub.size(), 1);
      ASS_EQ(info->substitutionForBanksSub[0].apply(0), TermList(a));
      ASS_EQ(env.getMainProblem(), &problem);
      ASS(env.initiallyHasNonDefaultSorts());
      ASS(!env.replayRecording);
      ASS_EQ(left->store(), leftStore);
      ASS_EQ(left->age(), 17);
    }
  }
  ASS_EQ(env.getMainProblem(), &problem);
  ASS(!env.replayRecording);
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
  auto info = replayer.replayInference(goal);
  ASS(info);
  const auto& extra = env.proofExtra.get<Inferences::TwoLiteralInferenceExtra>(goal);
  const auto& constraints = env.proofExtra.get<Inferences::ConstraintInformation>(goal);
  ASS_EQ(extra.get<Inferences::LiteralInferenceExtra>().literal(), (*left)[0]);
  ASS_EQ(extra.get<Inferences::OtherLiteralInferenceExtra>().literal(), (*right)[0]);
  ASS_EQ(constraints.literals.size(), 1);
  ASS_EQ(constraints.literals[0], (*goal)[1]);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), u);
  ASS_EQ(info->substitutionForBanksSub[1].apply(1), v);
  ASS_EQ(info->premises.size(), 2);
  const auto& leftPosition = extra.get<Inferences::LiteralInferenceExtra>().position;
  const auto& rightPosition = extra.get<Inferences::OtherLiteralInferenceExtra>().position;
  ASS(leftPosition);
  ASS(rightPosition);
  ASS_EQ(*leftPosition, 0);
  ASS_EQ(*rightPosition, 0);
  env.options->setUWA(oldUwa);
}

TEST_FUN(self_resolution_keeps_two_parent_banks)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  auto parent = clause({selected(~p(f(x))), selected(p(x))});
  TermList renamed = TermList::var(9);
  auto goal = clause({p(renamed), ~p(f(f(renamed)))},
      GeneratingInference2(InferenceRule::RESOLUTION, parent, parent));
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("literal_maximality_aftercheck", "off");
  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  auto info = replayer.replayInference(goal);
  ASS(info);
  ASS_EQ(info->premises.size(), 2);
  ASS_EQ(info->premises[0], parent);
  ASS_EQ(info->premises[1], parent);
  ASS_EQ(info->substitutionForBanksSub.size(), 2);
  auto mainValue = info->substitutionForBanksSub[0].apply(0);
  auto otherValue = info->substitutionForBanksSub[1].apply(0);
  ASS((mainValue == renamed && otherValue == TermList(f(renamed))) ||
      (otherValue == renamed && mainValue == TermList(f(renamed))));
}

static void replayRewriteWithIndependentParentBanks(InferenceRule rule, bool reverseEquality = false)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  auto main = clause({selected(p(f(x)))});
  auto equality = clause({selected(reverseEquality ? y == f(y) : f(y) == y)});
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
  auto info = replayer.replayInference(goal);
  ASS(info);
  ASS_EQ(info->substitutionForBanksSub.size(), 2);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
  ASS_EQ(info->substitutionForBanksSub[1].apply(1), renamed);
  const Inferences::RewriteInferenceExtra* rewrite;
  if (rule == InferenceRule::SUPERPOSITION) {
    const auto& extra = env.proofExtra.get<Inferences::SuperpositionExtra>(goal);
    const auto& literals = extra.get<Inferences::TwoLiteralInferenceExtra>();
    const auto& rewritePart = extra.get<Inferences::RewriteInferenceExtra>();
    ASS_EQ(literals.get<Inferences::LiteralInferenceExtra>().literal(), (*main)[0]);
    ASS_EQ(literals.get<Inferences::OtherLiteralInferenceExtra>().literal(), (*equality)[0]);
    ASS_EQ(rewritePart.get<Inferences::RewriteLhsInferenceExtra>().term(), TermList(f(y)));
    ASS_EQ(rewritePart.get<Inferences::RewriteTargetInferenceExtra>().term(), TermList(f(x)));
    ASS(env.proofExtra.get<Inferences::ConstraintInformation>(goal).literals.empty());
    ASS_EQ(&env.proofExtra.get<Inferences::RewriteInferenceExtra>(goal), &rewritePart);
    rewrite = &rewritePart;
  } else {
    const auto& extra = env.proofExtra.get<Inferences::RewriteInferenceExtra>(goal);
    ASS_EQ(extra.get<Inferences::RewriteLhsInferenceExtra>().term(), TermList(f(y)));
    ASS_EQ(extra.get<Inferences::RewriteTargetInferenceExtra>().term(), TermList(f(x)));
    rewrite = &extra;
  }
  const auto& targetPosition = rewrite->get<
      Inferences::TermReferenceInferenceExtra<Inferences::ReferenceTag::Main>>().position;
  const auto& equalityPosition = rewrite->get<
      Inferences::TermReferenceInferenceExtra<Inferences::ReferenceTag::Other>>().position;
  ASS(targetPosition);
  ASS(equalityPosition);
  ASS_EQ(*targetPosition, 0);
  ASS_EQ(*equalityPosition, 0);
}

TEST_FUN(superposition_applicators_preserve_parent_banks)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::SUPERPOSITION);
}

TEST_FUN(demodulation_applicators_preserve_original_variable_names)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::FORWARD_DEMODULATION);
}

TEST_FUN(superposition_recovers_replacement_from_reversed_equality)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::SUPERPOSITION, true);
}

TEST_FUN(demodulation_recovers_replacement_from_reversed_equality)
{
  replayRewriteWithIndependentParentBanks(InferenceRule::FORWARD_DEMODULATION, true);
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

TEST_FUN(native_replay_prints_extras_with_proof_extra_off)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto parent = clause({selected(p(x)), p(a)});
  auto goal = clause({p(a)}, GeneratingInference1(InferenceRule::FACTORING, parent));
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  ASS_EQ(env.options->proof(), Shell::Options::Proof::ON);
  ASS_EQ(env.options->proofExtra(), Shell::Options::ProofExtra::OFF);
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP();
  std::ostringstream disabled;
  store->outputProof(disabled, goal);
  ASS(disabled.str().find("parents=[") == std::string::npos);

  // Without a saved ordering, print the original step without replay extras.
  env.options->set("replay", "on");
  std::ostringstream noOrdering;
  store->outputProof(noOrdering, goal);
  ASS_EQ(noOrdering.str(), disabled.str());
  ASS(!env.proofExtra.find(goal));

  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream enabled;
  store->outputProof(enabled, goal);
  ASS(enabled.str().find("parents=[" + std::to_string(parent->number()) + ":[0 -> a]]") != std::string::npos);
  ASS(env.proofExtra.find(goal)->findComponent<InferenceReplayInformation>());
  ASS_EQ(env.options->proofExtra(), Shell::Options::ProofExtra::OFF);

  std::ostringstream repeated;
  store->outputProof(repeated, goal);
  ASS_EQ(repeated.str(), enabled.str());
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
  InferenceRecorder recording(goal);
  auto recorder = &recording;
  recorder->factoring(wrongCounts, parent, {&identity}, (*parent)[1], (*parent)[0]);
  ASS(!recorder->information());
  recorder->factoring(merging, parent, {&identity}, (*parent)[1], (*parent)[0]);
  ASS(!recorder->information());
  recorder->factoring(correct, parent, {&identity}, (*parent)[1], (*parent)[0]);
  auto info = recorder->information();
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
  InferenceRecorder recording(goal);
  auto recorder = &recording;
  recorder->factoring(candidate, parent, {&identity}, (*parent)[1], (*parent)[0]);
  auto info = recorder->information();
  ASS(info);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
}

namespace {
struct TrackedExtra : Lib::InferenceExtra {
  explicit TrackedExtra(bool& destroyed) : destroyed(destroyed) {}
  ~TrackedExtra() override { destroyed = true; }
  void output(std::ostream& out) const override { out << "original"; }
  bool& destroyed;
};
}

TEST_FUN(replay_replaces_existing_extra_only_on_success)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s})
  auto parent = clause({selected(p(x)), p(a)});
  auto goal = clause({p(a)}, GeneratingInference1(InferenceRule::FACTORING, parent));
  auto unmatched = clause({q(a)}, GeneratingInference1(InferenceRule::FACTORING, parent));
  auto unsupported = clause({p(a)}, SimplifyingInference1(InferenceRule::REORDER_LITERALS, parent));
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("proof_extra", "full");
  bool replaced = false, unmatchedDestroyed = false, unsupportedDestroyed = false;
  env.proofExtra.insert(goal, new TrackedExtra(replaced));
  auto unmatchedExtra = new TrackedExtra(unmatchedDestroyed);
  env.proofExtra.insert(unmatched, unmatchedExtra);
  auto unsupportedExtra = new TrackedExtra(unsupportedDestroyed);
  env.proofExtra.insert(unsupported, unsupportedExtra);

  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  auto info = replayer.replayInference(goal);
  ASS(info);
  ASS(replaced);
  ASS_EQ(env.proofExtra.find(goal)->findComponent<Inferences::InferenceReplayInformation>(), info);
  ASS_EQ(info->conclusion, goal);
  ASS_EQ(info->premises[0], parent);
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), TermList(a));
  ASS(!env.proofExtra.find(goal)->toString().empty());

  // Each replay commits a fresh result even when an extra is already present.
  info = replayer.replayInference(goal);
  ASS(info);
  ASS_EQ(env.proofExtra.find(goal)->findComponent<Inferences::InferenceReplayInformation>(), info);
  ASS_EQ(info->conclusion, goal);
  // A later failed attempt must preserve even a previously replayed extra.
  parent->setSelected(0);
  ASS(!replayer.replayInference(goal));
  ASS_EQ(env.proofExtra.find(goal)->findComponent<Inferences::InferenceReplayInformation>(), info);
  parent->setSelected(1);
  ASS(!replayer.replayInference(unmatched));
  ASS(!unmatchedDestroyed);
  ASS_EQ(env.proofExtra.find(unmatched), unmatchedExtra);
  ASS(!replayer.replayInference(unsupported));
  ASS(!unsupportedDestroyed);
  ASS_EQ(env.proofExtra.find(unsupported), unsupportedExtra);

  env.proofExtra.remove(unmatched);
  env.proofExtra.remove(unsupported);
  env.proofExtra.remove(goal);
}

TEST_FUN(clause_destruction_removes_replay_extras_with_proof_extra_off)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  auto parent = clause({p(x)});
  auto goal = clause({p(x)}, GeneratingInference1(InferenceRule::FACTORING, parent));
  env.options->set("proof_extra", "off");
  env.options->set("replay", "on");
  bool destroyed = false;
  env.proofExtra.insert(goal, new TrackedExtra(destroyed));
  goal->destroy();
  ASS(destroyed);
}
