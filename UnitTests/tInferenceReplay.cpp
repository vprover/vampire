/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Lib/SharedSet.hpp"
#include "Shell/ACReconstruction.hpp"
#include "Shell/CNF.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Options.hpp"
#include "Shell/FunctionDefinition.hpp"
#include "Shell/Rectify.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/TPTPReplayProofPrinter.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Parse/TPTP.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"

#include <sstream>

using namespace Kernel;
using namespace Test;
using Shell::InferenceRecorder;

static Shell::InferenceRecorder::InferenceReplayAnnotation replay(Clause* goal)
{
  Shell::InferenceReplayer replayer;
  auto rule = goal->inference().rule();
  if (rule != InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION) {
    Problem problem;
    UnitList* units = nullptr;
    auto parents = goal->getParents();
    while (parents.hasNext()) { UnitList::push(parents.next(), units); }
    problem.addUnits(units);
    env.options->resolveAwayAutoValues0();
    env.options->resolveAwayAutoValues(problem);
    replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  }
  auto annotation = Shell::InferenceRecorder::inferenceReplayAnnotation(goal, replayer, true);
  return annotation;
}

static std::string renderedReplay(Clause* goal, const Shell::InferenceRecorder::InferenceReplayAnnotation& annotation)
{
  return Kernel::formatTPTPReplayAnnotations(goal, annotation);
}

static void ac(Clause* goal, const Shell::InferenceRecorder::InferenceReplayAnnotation& annotation,
               std::initializer_list<unsigned> expected)
{
  auto core = annotation.naturalLiterals;
  std::vector<unsigned> permutation;
  bool bridge = Shell::ACReconstruction::clauseOrderBridge(goal, goal->inference().rule(),
      annotation.information, core, permutation);
  ASS_EQ(bridge, expected.size() != 0);
  if (expected.size()) {
    ASS_EQ(permutation.size(), expected.size());
    unsigned i = 0;
    for (unsigned index : expected) {
      ASS_EQ(permutation[i], index);
      ASS_EQ(core[index], (*goal)[i]);
      ++i;
    }
  }
  // Exercise the actual printer too: annotations belong to the natural rule
  // node, and the displayed conclusion points to that node through AC.
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("proof", "tstp-ac");
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream out;
  store->outputProof(out, goal);
  ASS(out.str().find(renderedReplay(goal, annotation)) != std::string::npos);
  if (bridge) {
    std::string coreId = "f" + std::to_string(goal->number()) + "_vh_" + ruleName(goal->inference().rule());
    // The printer's rule names replace spaces with underscores.
    for (char& c : coreId) { if (c == ' ') { c = '_'; } }
    ASS(out.str().find(Shell::ACReconstruction::acInference(coreId, permutation)) != std::string::npos);
  }
  std::istringstream input(out.str());
  Parse::TPTP parser(input, "replay-proof.tstp");
  parser.parse();
}

TEST_FUN(binary_resolution_replay_skips_partial_redundancy_with_avatar_splits)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  env.options->set("partial_redundancy_check", "on");
  env.options->set("partial_redundancy_avatar_constraints", "on");
  env.options->set("partial_redundancy_literal_constraints", "on");
  env.options->set("avatar", "on");
  auto left = clause({selected(~p(x)), q(x)});
  auto right = clause({selected(p(a))});
  // These are search-time levels, absent from the replay engine's splitter.
  // Calling handleResolution during replay would try to register an entry
  // against level 200 in Splitter::addPartialRedundancyEntry.
  left->setSplits(SplitSet::getEmpty());
  right->setSplits(SplitSet::getSingleton(200));
  auto goal = clause({q(a)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  auto annotation = replay(goal);
  ASS(annotation.information);
  auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks.size(), 2);
  ASS_EQ(banks[0].apply(0), TermList(a));
  ASS(renderedReplay(goal, annotation).find("unifier([subs(") != std::string::npos);
  ASS(renderedReplay(goal, annotation).find("resolved_literals([literal(") != std::string::npos);
}

TEST_FUN(replay_preserves_environment_and_parent_state)
{
  DECL_DEFAULT_VARS
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_PRED(p, {s})
  DECL_PRED(q, {s})
  auto left = clause({selected(~p(x)), q(x)});
  auto right = clause({selected(p(a))});
  auto goal = clause({q(a)}, GeneratingInference2(InferenceRule::RESOLUTION, left, right));
  left->setAge(17);
  right->setAge(32);
  auto leftStore = left->store();
  auto rightStore = right->store();
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
      ASS(InferenceRecorder::instance()->getLastRecordedInferenceInformation());
      ASS_EQ(env.getMainProblem(), &problem);
      ASS(env.initiallyHasNonDefaultSorts());
      ASS(!env.reconstruction);
      ASS_EQ(left->store(), leftStore);
      ASS_EQ(right->store(), rightStore);
      ASS_EQ(left->age(), 17);
      ASS_EQ(right->age(), 32);
    }
  }
  ASS_EQ(env.getMainProblem(), &problem);
  ASS(!env.reconstruction);
  ASS_EQ(InferenceStore::instance()->ordering.ptr(), savedOrdering.ptr());
}

TEST_FUN(replay_matching_preserves_renamed_duplicate_occurrences)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto parent = clause({p(x), p(x), q(x), q(x)});
  TermList renamed = TermList::var(9);
  auto goal = clause({q(renamed), p(renamed), p(renamed)},
      SimplifyingInference1(InferenceRule::CONDENSATION, parent));
  auto wrong = clause({p(x), q(x), q(x)},
      SimplifyingInference1(InferenceRule::CONDENSATION, parent));
  auto correct = clause({p(x), p(x), q(x)},
      SimplifyingInference1(InferenceRule::CONDENSATION, parent));
  auto recorder = InferenceRecorder::instance();
  recorder->setCurrentGoal(goal);
  auto kind = InferenceRecorder::InferenceInformation::LiteralPositionKind::REMOVED;
  ASS(!recorder->recordReplayedInferenceCandidate(wrong, {parent}, std::vector<Substitution>(1), kind, {{0, 3}}));
  ASS(!recorder->getLastRecordedInferenceInformation());
  ASS(recorder->recordReplayedInferenceCandidate(correct, {parent}, std::vector<Substitution>(1), kind, {{0, 3}}));
  const auto* info = recorder->getLastRecordedInferenceInformation();
  ASS_EQ(info->substitutionForBanksSub[0].apply(0), renamed);
  ASS_EQ(info->naturalLiterals[0], p(renamed));
  ASS_EQ(info->naturalLiterals[1], p(renamed));
  ASS_EQ(info->naturalLiterals[2], q(renamed));
}

TEST_FUN(rectification_records_leancheck_binder_permutation_inside_terms)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort, sort}, sort)
  DECL_PRED(p, {sort})
  env.options->set("replay", "on");
  auto parent = new FormulaUnit(new QuantifiedFormula(FORALL,
      VSList::cons({1, sort}, VSList::cons({0, sort}, nullptr)),
      new AtomicFormula(p(f(x, y)))), FromInput(UnitInputType::AXIOM));
  auto goal = Shell::Rectify::rectify(parent);
  ASS(goal->inference().rule() == InferenceRule::RECTIFY);
  const auto* info = InferenceRecorder::instance()->getRectificationReplayInformation(goal->number());
  ASS(info);
  ASS_EQ(info->scopes.size(), 1);
  const auto& scope = info->scopes[0];
  ASS_EQ(scope.renaming.apply(0), TermList::var(1));
  ASS_EQ(scope.renaming.apply(1), TermList::var(0));
  ASS_EQ(SubstHelper::apply(TermList(f(x, y)), scope.renaming), TermList(f(y, x)));
  ASS_EQ(Kernel::tptpRectificationReplayAnnotation(goal, true),
      "rectify([postorder([scope([before([X1,X0]),after([X0,X1]),substitution([b(X0,X1),b(X1,X0)])])])])");
  ASS(Kernel::tptpRectificationReplayAnnotation(goal, false).empty());
}

TEST_FUN(rectification_records_eliminated_binders_and_respects_keep_unused)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  env.options->set("replay", "on");
  auto parent = new FormulaUnit(new QuantifiedFormula(FORALL,
      VSList::cons({7, sort}, nullptr), new AtomicFormula(p(a))), FromInput(UnitInputType::AXIOM));
  auto removed = Shell::Rectify::rectify(parent);
  ASS_EQ(Kernel::tptpRectificationReplayAnnotation(removed, true),
      "rectify([postorder([scope([before([X7]),after([]),removed([X7])])])])");
  auto kept = Shell::Rectify::rectify(parent, /*removeUnusedVars=*/false);
  const auto* info = InferenceRecorder::instance()->getRectificationReplayInformation(kept->number());
  ASS(info);
  ASS_EQ(info->scopes.size(), 1);
  ASS(info->scopes[0].removed.empty());
  ASS_EQ(info->scopes[0].targetBinders.size(), 1);
  ASS(Kernel::tptpRectificationReplayAnnotation(kept, true).empty());
}

TEST_FUN(extensionality_resolution_substitutions_and_ac)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto ext = clause({x.sort(sort) == y, p(x), q(y)});
  auto other = clause({selected(f(z) != a), r(z)});
  TermList v = TermList::var(8);
  auto goal = clause({r(v), q(a), p(f(v))},
      GeneratingInference2(InferenceRule::EXTENSIONALITY_RESOLUTION, ext, other));
  auto annotation = replay(goal);
  ASS(annotation.information);
  auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks.size(), 2);
  ASS_EQ(banks[0].apply(0), TermList(f(v)));
  ASS_EQ(banks[0].apply(1), TermList(a));
  ASS_EQ(banks[1].apply(2), v);
  ASS(renderedReplay(goal, annotation).find("resolved_literals([literal(") != std::string::npos);
  ac(goal, annotation, {2, 1, 0});
}

TEST_FUN(forward_literal_rewriting_substitutions_and_ac)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  DECL_PRED(s, {sort})
  auto main = clause({q(x), p(f(x)), r(x)});
  auto side = clause({~p(y), s(y)});
  TermList v = TermList::var(9);
  auto goal = clause({s(f(v)), q(v), r(v)},
      SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(1), TermList(f(v)));
  ASS(renderedReplay(goal, annotation).find("rewritten_literal(literal(f" + std::to_string(main->number()) + ",1))") != std::string::npos);
  ac(goal, annotation, {1, 0, 2});
}

TEST_FUN(forward_literal_rewriting_negative_literal_without_counterpart)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(s, {sort})
  auto main = clause({q(x), ~p(f(x))});
  auto side = clause({s(y), p(y)});
  TermList v = TermList::var(9);
  auto goal = clause({s(f(v)), q(v)},
      SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(1), TermList(f(v)));
  auto& positions = annotation.information->literalPositions;
  ASS_EQ(positions.size(), 2);
  ASS_EQ(positions[0].literalIndex, 1);
  ASS_EQ(positions[1].literalIndex, 1);
  ac(goal, annotation, {1, 0});
}

TEST_FUN(unit_resulting_resolution_composes_all_parent_banks)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({~p(x), ~q(f(x)), r(x)});
  auto first = clause({p(y)});
  auto second = clause({q(f(a))});
  UnitList* parents = nullptr;
  UnitList::push(second, parents);
  UnitList::push(first, parents);
  UnitList::push(main, parents);
  auto goal = clause({r(a)}, GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, parents));
  auto annotation = replay(goal);
  ASS(annotation.information);
  auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks.size(), 3);
  ASS_EQ(banks[0].apply(0), TermList(a));
  ASS_EQ(banks[1].apply(1), TermList(a));
  ASS_EQ(annotation.information->literalPositions.size(), 4);
  ac(goal, annotation, {});
}

TEST_FUN(unit_resulting_resolution_repeated_parent_and_empty_goal)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {sort})
  auto main = clause({~p(a), ~p(b)});
  auto unit = clause({p(x)});
  UnitList* parents = nullptr;
  UnitList::push(unit, parents);
  UnitList::push(unit, parents);
  UnitList::push(main, parents);
  auto goal = clause(Stack<Lit>(), GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, parents));
  auto annotation = replay(goal);
  ASS(annotation.information);
  auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks.size(), 3);
  ASS_EQ(banks[1].apply(0), TermList(a));
  ASS_EQ(banks[2].apply(0), TermList(b));
}

TEST_FUN(subsumption_equality_resolution_preserves_surviving_names)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto main = clause({x.sort(sort) != y, p(y), q(y)});
  TermList v = TermList::var(9);
  auto goal = clause({q(v), p(v)},
      SimplifyingInference1(InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION, main));
  auto annotation = replay(goal);
  ASS(annotation.information);
  auto& subst = annotation.information->substitutionForBanksSub[0];
  ASS_EQ(subst.apply(0), v);
  ASS_EQ(subst.apply(1), v);
  ASS_EQ(annotation.information->literalPositions[0].literalIndex, 0);
  ac(goal, annotation, {1, 0});
}

TEST_FUN(backward_subsumption_resolution_matcher_and_ac)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(a), ~p(a), r(a)});
  auto side = clause({p(x), r(x)});
  auto goal = clause({r(a), q(a)},
      SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(0), TermList(a));
  ASS(renderedReplay(goal, annotation).find("subs(f" + std::to_string(side->number()) + ",[b(X0,a)])") != std::string::npos);
  ASS(renderedReplay(goal, annotation).find("removed_literals(literal(f" + std::to_string(main->number()) + ",1))") != std::string::npos);
  ac(goal, annotation, {1, 0});
}

TEST_FUN(constrained_resolution_constraints_substitutions_and_ac)
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
  auto oldUwa = env.options->unificationWithAbstraction();
  env.options->setUWA(Shell::Options::UnificationWithAbstraction::ALL);
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->constraints.size(), 1);
  ASS_EQ(annotation.information->constraints[0], (*goal)[1]);
  ASS(renderedReplay(goal, annotation).find("constraints([disequality($i,") != std::string::npos);
  ASS_EQ(annotation.information->substitutionForBanksSub[0].apply(0), u);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(1), v);
  ac(goal, annotation, {1, 0, 2});
  env.options->setUWA(oldUwa);
}

TEST_FUN(backward_demodulation_separate_banks_and_in_place_ac)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), p(f(f(x))), r(x)});
  // The two X0 occurrences are independent parent variables.
  auto side = clause({f(x) == x});
  TermList v = TermList::var(9);
  auto goal = clause({p(f(v)), q(v), r(v)},
      SimplifyingInference2(InferenceRule::BACKWARD_DEMODULATION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  const auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks.size(), 2);
  ASS_EQ(banks[0].apply(0), v);
  ASS_EQ(banks[1].apply(0), TermList(f(v)));
  ASS(renderedReplay(goal, annotation).find("rewrite([equality(literal(f" + std::to_string(side->number()) + ",0))") != std::string::npos);
  ac(goal, annotation, {1, 0, 2});
}

TEST_FUN(forward_subsumption_demodulation_context_and_subterm_bindings)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), p(g(f(x))), r(f(x))});
  auto side = clause({g(f(y)) == y, q(y)});
  TermList v = TermList::var(9);
  auto goal = clause({p(v), q(v), r(f(v))},
      SimplifyingInference2(InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(1), v);
  ASS_EQ(annotation.information->rewriteEquality.literalIndex, 0);
  ac(goal, annotation, {1, 0, 2});
}

TEST_FUN(backward_subsumption_demodulation_context_and_subterm_bindings)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), p(g(f(f(x)))), r(x)});
  // X0 is bound by context matching; X1 only by matching the rewrite subterm.
  // The main parent's X0 belongs to a separate substitution bank.
  auto side = clause({q(x), g(f(y)) == y});
  TermList v = TermList::var(9);
  auto goal = clause({p(f(v)), q(v), r(v)},
      SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  const auto& info = *annotation.information;
  ASS_EQ(info.substitutionForBanksSub.size(), 2);
  ASS_EQ(info.substitutionForBanksSub[0].apply(0), v);
  ASS_EQ(info.substitutionForBanksSub[1].apply(0), v);
  ASS_EQ(info.substitutionForBanksSub[1].apply(1), TermList(f(v)));
  ASS_EQ(info.rewriteEquality.premiseIndex, 1);
  ASS_EQ(info.rewriteEquality.literalIndex, 1);
  ASS_EQ(info.rewriteFrom, TermList(g(f(f(v)))));
  ASS_EQ(info.rewriteTo, TermList(f(v)));
  ASS(renderedReplay(goal, annotation).find("rewrite([equality(literal(f" + std::to_string(side->number()) + ",1))") != std::string::npos);
  ASS(renderedReplay(goal, annotation).find("rewritten_literal(literal(f" + std::to_string(main->number()) + ",1))") != std::string::npos);
  ac(goal, annotation, {1, 0, 2});
}

TEST_FUN(backward_subsumption_demodulation_replays_later_rewrite_candidate)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), p(g(f(x))), r(g(f(f(x))))});
  auto side = clause({q(x), g(f(y)) == y});
  TermList v = TermList::var(9);
  auto goal = clause({q(v), p(g(f(v))), r(f(v))},
      SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->literalPositions.size(), 1);
  ASS_EQ(annotation.information->literalPositions[0].literalIndex, 2);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(1), TermList(f(v)));
  ac(goal, annotation, {});
}

TEST_FUN(inner_rewriting_records_all_changed_literals)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), f(x) != x, p(f(x)), r(f(x))});
  TermList v = TermList::var(9);
  auto goal = clause({p(v), f(v) != v, q(v), r(v)},
      SimplifyingInference1(InferenceRule::INNER_REWRITING, main));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->literalPositions.size(), 2);
  ASS_EQ(annotation.information->rewriteEquality.literalIndex, 1);
  ASS(renderedReplay(goal, annotation).find("rewritten_literals([") != std::string::npos);
  ac(goal, annotation, {2, 1, 0, 3});
}

TEST_FUN(constrained_superposition_constraints_suffix_and_in_place_ac)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({q(x), p(f(x))});
  auto side = clause({g(y) == y, r(y)});
  main->setSelected(main->length());
  side->setSelected(1);
  env.options->set("literal_maximality_aftercheck", "off");
  TermList u = TermList::var(8), v = TermList::var(9);
  auto goal = clause({p(v), q(u), r(v), f(u) != g(v)},
      GeneratingInference2(InferenceRule::CONSTRAINED_SUPERPOSITION, main, side));
  auto oldUwa = env.options->unificationWithAbstraction();
  env.options->setUWA(Shell::Options::UnificationWithAbstraction::ALL);
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->constraints.size(), 1);
  ASS_EQ(annotation.information->constraints[0], (*goal)[3]);
  ASS_EQ(annotation.information->rewriteFrom, TermList(f(u)));
  ASS_EQ(annotation.information->rewriteTo, v);
  ac(goal, annotation, {1, 0, 2, 3});
  env.options->setUWA(oldUwa);
}

static Clause* preprocessing(std::initializer_list<Lit> natural, Inference inference,
                             std::initializer_list<unsigned> printedOrder)
{
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  Clause* goal = clause(Stack<Lit>(natural), std::move(inference));
  Shell::ACReconstruction::recordPreprocessingOrder(goal);
  std::vector<Literal*> literals(goal->begin(), goal->end());
  unsigned i = 0;
  for (unsigned source : printedOrder) { (*goal)[i++] = literals[source]; }
  return goal;
}

// Simulate selection after the lightweight hook at each inference's result
// creation site. Ordinary Clause construction does not record any order.
TEST_FUN(preprocessing_inference_local_order_bridges)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  env.options->set("proof", "tstp-ac");
  auto parent = clause({p(x), q(x), r(x)});
  for (auto rule : {InferenceRule::INEQUALITY_SPLITTING,
                    InferenceRule::EQUALITY_PROXY_REPLACEMENT,
                    InferenceRule::DEFINITION_UNFOLDING}) {
    env.reconstruction = false;
    auto goal = preprocessing({p(x), q(x), r(x)}, NonspecificInference1(rule, parent), {2, 1, 0});
    ac(goal, {}, {2, 1, 0});
  }
  env.reconstruction = false;
  auto unchanged = preprocessing({p(x), q(x)}, NonspecificInference1(InferenceRule::DEFINITION_UNFOLDING, parent), {});
  ac(unchanged, {}, {});
}

TEST_FUN(equality_proxy_axiom_order_without_clause_parent)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  auto proxySymbol = env.signature->addFreshPredicate(OperatorType::getPredicateType({sort, sort}), "sQ")->markEqualityProxy();
  auto sQ = PredSugar(proxySymbol->number());
  auto definition = new FormulaUnit(Formula::trueFormula(), FromInput(UnitInputType::AXIOM));
  auto goal = preprocessing({~sQ(x, y), ~p(x), p(y)},
      NonspecificInference1(InferenceRule::EQUALITY_PROXY_AXIOM, definition), {2, 0, 1});
  ac(goal, {}, {2, 0, 1});
}

TEST_FUN(preprocessing_replacement_literals_preserve_parent_occurrences)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(sP, {sort})
  auto proxySymbol = env.signature->addFreshPredicate(OperatorType::getPredicateType({sort, sort}), "sQ")->markEqualityProxy();
  auto sQ = PredSugar(proxySymbol->number());
  auto parent = clause({p(x), x.sort(sort) != f(a), q(x)});
  auto name = clause({~sP(f(a))},
      NonspecificInference0(UnitInputType::AXIOM, InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION));
  auto split = preprocessing({p(x), sP(x), q(x)},
      NonspecificInference2(InferenceRule::INEQUALITY_SPLITTING, parent, name), {2, 1, 0});
  ac(split, {}, {2, 1, 0});
  auto proxy = preprocessing({p(x), ~sQ(x, f(a)), q(x)},
      NonspecificInference1(InferenceRule::EQUALITY_PROXY_REPLACEMENT, parent), {2, 1, 0});
  ac(proxy, {}, {2, 1, 0});
}

TEST_FUN(inequality_splitting_duplicate_source_occurrences)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(first, {sort})
  DECL_PRED(second, {sort})
  auto parent = clause({p(x), x.sort(sort) != f(a), x.sort(sort) != f(a)});
  auto defFirst = clause({~first(f(a))});
  auto defSecond = clause({~second(f(a))});
  UnitList* parents = nullptr;
  UnitList::push(defFirst, parents);
  UnitList::push(defSecond, parents);
  UnitList::push(parent, parents);
  auto goal = preprocessing({p(x), first(x), second(x)},
      NonspecificInferenceMany(InferenceRule::INEQUALITY_SPLITTING, parents), {2, 0, 1});
  ac(goal, {}, {2, 0, 1});
}

TEST_FUN(definition_unfolding_records_result_with_nested_substitutions)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_FUNC(g, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto parent = clause({p(g(g(x))), q(x)});
  auto definition = clause({f(y) == g(y)});
  auto goal = preprocessing({p(f(f(x))), q(x)},
      NonspecificInference2(InferenceRule::DEFINITION_UNFOLDING, parent, definition), {1, 0});
  ac(goal, {}, {1, 0});
}

TEST_FUN(definition_unfolding_preserves_existing_full_proof_extra)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto parent = clause({p(b), q(b)});
  auto definition = clause({a == b});
  auto goal = clause({p(a), q(a)},
      NonspecificInference2(InferenceRule::DEFINITION_UNFOLDING, parent, definition));
  env.proofExtra.insert(goal, new Shell::FunctionDefinitionExtra({TermList(b).term()}));
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  Shell::ACReconstruction::recordPreprocessingOrder(goal);
  ASS_EQ(env.proofExtra.get<Shell::FunctionDefinitionExtra>(goal).lhs[0], TermList(b).term());
  std::swap((*goal)[0], (*goal)[1]);
  ac(goal, {}, {1, 0});
}

TEST_FUN(general_splitting_component_and_conclusion_bridges)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  DECL_PRED(sP, {sort})
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  env.reconstruction = false;
  auto parent = clause({p(x), q(x), r(x)});
  auto component = clause({p(x), q(x), sP(x)},
      NonspecificInference0(UnitInputType::AXIOM, InferenceRule::GENERAL_SPLITTING_COMPONENT));
  Shell::ACReconstruction::recordPreprocessingOrder(component);
  InferenceStore::instance()->recordSplittingNameLiteral(component, sP(x));
  auto goal = clause({r(x), ~sP(x)},
      NonspecificInference2(InferenceRule::GENERAL_SPLITTING, parent, component));
  Shell::ACReconstruction::recordPreprocessingOrder(goal);
  std::swap((*component)[0], (*component)[2]);
  std::swap((*goal)[0], (*goal)[1]);
  // Component clauses are printed using cnf_transformation, not their internal
  // rule name. Check both custom printer paths and their parent references.
  std::vector<Literal*> core;
  std::vector<unsigned> permutation;
  ASS(Shell::ACReconstruction::clauseOrderBridge(component, component->inference().rule(), nullptr, core, permutation));
  ASS_EQ(permutation.size(), 3);
  ASS_EQ(permutation[0], 2);
  ASS_EQ(permutation[1], 1);
  ASS_EQ(permutation[2], 0);
  ac(goal, {}, {1, 0});
  std::ostringstream out;
  InferenceStore::instance()->outputProof(out, goal);
  std::string componentId = "f" + std::to_string(component->number());
  std::string coreId = componentId + "_vh_cnf_transformation";
  ASS(out.str().find(Shell::ACReconstruction::acInference(coreId, {2, 1, 0})) != std::string::npos);
  ASS(out.str().find("inference(cnf_transformation,[],[" + componentId + "_D])") != std::string::npos);
  ASS(out.str().find("inference(general_splitting,[],[f" + std::to_string(parent->number()) + "," + componentId + "_D])") != std::string::npos);
  ASS(out.str().find(componentId + "_D,") < out.str().find(coreId + ","));
}

TEST_FUN(clausification_certificate_binders_duplicates_permutation_and_symmetry)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  FormulaList* literals = nullptr;
  FormulaList::push(new AtomicFormula(q(y)), literals);
  FormulaList::push(new AtomicFormula(p(x)), literals);
  Literal* equality = x.sort(sort) == y;
  FormulaList::push(new AtomicFormula(equality, /*flipForPrinting=*/true), literals);
  FormulaList::push(new AtomicFormula(p(x)), literals);
  VSList* binders = VSList::cons({1, sort}, VSList::cons({0, sort}, nullptr));
  auto parent = new FormulaUnit(new QuantifiedFormula(FORALL, binders,
      JunctionFormula::generalJunction(OR, literals)), FromInput(UnitInputType::AXIOM));
  Shell::CNF cnf;
  ClauseStack clauses;
  cnf.clausify(parent, clauses);
  ASS_EQ(clauses.size(), 1);
  Clause* goal = clauses[0];
  // Simulate selection's final ordering. The certificate uses the printed
  // parent's order q(y), p(x), y=x, p(x), retaining both p(x) occurrences.
  (*goal)[0] = p(x);
  (*goal)[1] = equality;
  (*goal)[2] = q(y);
  (*goal)[3] = p(x);
  auto annotation = Kernel::tptpClausificationReplayAnnotation(goal, true);
  ASS_EQ(annotation,
      "binder_mapping([b(X1,X1),b(X0,X0)]),literal_permutation([1,2,0,3]),swapped_equalities([1])");
  ASS(env.proofExtra.find(goal));
  ASS(Kernel::tptpClausificationReplayAnnotation(goal, false).empty());
  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  InferenceStore::instance()->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream out;
  InferenceStore::instance()->outputProof(out, goal);
  ASS(out.str().find("inference(cnf_transformation,[" + annotation + "],[f" +
      std::to_string(parent->number()) + "])") != std::string::npos);
  std::istringstream input(out.str());
  Parse::TPTP parser(input, "cnf-certificate.tstp");
  parser.parse();
  // Changing a literal cannot be hidden by guessing a different substitution.
  (*goal)[1] = x.sort(sort) == z;
  ASS(Kernel::tptpClausificationReplayAnnotation(goal, true).empty());
}

TEST_FUN(clausification_certificate_identity_ground_and_empty_clause)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  Shell::CNF cnf;
  ClauseStack clauses;
  auto source = clause({p(x), p(x), p(a)});
  auto parent = new FormulaUnit(Formula::fromClause(source), FromInput(UnitInputType::AXIOM));
  cnf.clausify(parent, clauses);
  auto goal = clauses.pop();
  (*goal)[0] = p(x);
  (*goal)[1] = p(a);
  (*goal)[2] = p(x);
  ASS_EQ(Kernel::tptpClausificationReplayAnnotation(goal, true),
      "binder_mapping([b(X0,X0)]),literal_permutation([0,2,1]),swapped_equalities([])");
  auto groundParent = new FormulaUnit(new AtomicFormula(p(a)), FromInput(UnitInputType::AXIOM));
  cnf.clausify(groundParent, clauses);
  ASS_EQ(Kernel::tptpClausificationReplayAnnotation(clauses.pop(), true),
      "binder_mapping([]),literal_permutation([0]),swapped_equalities([])");
  auto falseParent = new FormulaUnit(Formula::falseFormula(), FromInput(UnitInputType::AXIOM));
  cnf.clausify(falseParent, clauses);
  ASS_EQ(Kernel::tptpClausificationReplayAnnotation(clauses.pop(), true),
      "binder_mapping([]),literal_permutation([]),swapped_equalities([])");
  // Capture is controlled only by proof_extra, independently of replay.
  env.options->set("proof", "tptp");
  env.options->set("replay", "off");
  cnf.clausify(groundParent, clauses);
  auto recorded = clauses.pop();
  ASS(env.proofExtra.find(recorded));
  ASS(!Kernel::tptpClausificationReplayAnnotation(recorded, true).empty());
  ASS(Kernel::tptpClausificationReplayAnnotation(recorded, false).empty());
  env.options->set("proof", "tstp-ac");
  for (auto mode : {"off", "full"}) {
    env.options->set("proof_extra", mode);
    cnf.clausify(groundParent, clauses);
    auto disabled = clauses.pop();
    ASS(!env.proofExtra.find(disabled));
    ASS(Kernel::tptpClausificationReplayAnnotation(disabled, true).empty());
  }
}

TEST_FUN(clausification_recording_rejects_vacuous_binders_and_general_formulas)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  env.options->set("proof_extra", "replay");
  Shell::CNF cnf;
  ClauseStack clauses;
  auto vacuous = new FormulaUnit(new QuantifiedFormula(FORALL,
      VSList::cons({0, sort}, nullptr), new AtomicFormula(p(a))), FromInput(UnitInputType::AXIOM));
  cnf.clausify(vacuous, clauses);
  ASS_EQ(clauses.size(), 1);
  ASS(!env.proofExtra.find(clauses.pop()));
  FormulaList* conjuncts = nullptr;
  FormulaList::push(new AtomicFormula(p(a)), conjuncts);
  FormulaList::push(new AtomicFormula(q(a)), conjuncts);
  auto conjunction = new FormulaUnit(JunctionFormula::generalJunction(AND, conjuncts),
      FromInput(UnitInputType::AXIOM));
  cnf.clausify(conjunction, clauses);
  ASS_EQ(clauses.size(), 2);
  while (clauses.isNonEmpty()) { ASS(!env.proofExtra.find(clauses.pop())); }
}

TEST_FUN(avatar_split_instantiation_survives_negative_ground_definitions)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  Literal* ground = ~q(a);
  auto seed = clause({p(x), ground});
  seed->setSplits(SplitSet::getEmpty());
  env.reconstruction = false;
  env.options->set("proof", "tstp-ac");
  env.options->set("proof_extra", "replay");
  env.options->set("avatar_add_complementary", "none");
  Problem problem;
  problem.addUnits(UnitList::singleton(seed));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  FormulaUnit* goal = nullptr;
  std::string expected;
  {
    MockedSaturationAlgorithm alg(problem, *env.options);
    Saturation::Splitter splitter;
    splitter.init(&alg);
    ASS(splitter.doSplitting(seed));
    Unit* variableDefinition = nullptr;
    for (unsigned name = 0; name < splitter.splitLevelCnt(); ++name) {
      if (splitter.isUsedName(name) && !(*splitter.getComponentClause(name))[0]->ground()) {
        variableDefinition = splitter.getDefinitionFromName(name);
        break;
      }
    }
    ASS(variableDefinition);
    auto groundName = splitter.satNaming().toSAT(ground);
    Unit* groundDefinition = splitter.getDefinitionFromName(splitter.getNameFromLiteral(groundName));
    ASS(env.proofExtra.find(variableDefinition));
    ASS(!env.proofExtra.find(groundDefinition));
    UnitList* parents = nullptr;
    UnitList::push(variableDefinition, parents);
    UnitList::push(groundDefinition, parents);
    UnitList::push(seed, parents);
    goal = new FormulaUnit(new Formula(true),
        NonspecificInferenceMany(InferenceRule::AVATAR_SPLIT_CLAUSE, parents));
    expected = "post_rewrite_instantiation([b(X0,arg(f" +
        std::to_string(variableDefinition->number()) + ",X0))])";
    ASS_EQ(Kernel::tptpAvatarSplitInstantiationReplayAnnotation(goal), expected);
  }
  std::ostringstream out;
  InferenceStore::instance()->outputProof(out, goal);
  ASS(out.str().find(expected) != std::string::npos);
  std::istringstream input(out.str());
  Parse::TPTP parser(input, "avatar-split.tstp");
  parser.parse();
}

TEST_FUN(avatar_conversion_preserves_occurrences_and_original_naming)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_FUNC(f, {sort}, sort)
  Literal* eq = a == b;
  Literal* neq = f(a) != f(b);
  auto seed = clause({eq, neq});
  seed->setSplits(SplitSet::getEmpty());
  Unit* origin = nullptr;
  std::vector<Unit*> definitions;
  std::string expected;
  env.reconstruction = false;
  env.options->set("proof", "tptp-ac");
  Problem problem;
  problem.addUnits(UnitList::singleton(seed));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  {
    MockedSaturationAlgorithm alg(problem, *env.options);
    Saturation::Splitter splitter;
    splitter.init(&alg);
    bool split = splitter.doSplitting(seed);
    ASS(split);
    auto eqName = splitter.satNaming().toSAT(eq);
    auto neqName = splitter.satNaming().toSAT(neq);
    Unit* eqDefinition = splitter.getDefinitionFromName(splitter.getNameFromLiteral(eqName));
    Unit* neqDefinition = splitter.getDefinitionFromName(splitter.getNameFromLiteral(neqName));
    LiteralStack core;
    core.push(eq);
    core.push(neq);
    core.push(eq);
    SAT::SATClause* converted = splitter.satNaming().createConflictClause(core);
    // Duplicate removal leaves the original conversion behind a PropInference.
    ASS_EQ(converted->inference()->getType(), SAT::SATInference::PROP_INF);
    SAT::SATInference::visitFOConversions(converted, [&](SAT::SATClause* conversion) {
      origin = conversion->inference()->foConversion()->getOrigin();
    });
    ASS(origin);
    // Both full and replay capture the conversion. Capture is independent of
    // proof format, and recording the same conversion again is idempotent.
    env.options->set("proof", "tptp");
    env.options->set("proof_extra", "full");
    splitter.recordAvatarConversion(converted);
    auto fullAnnotation = Kernel::tptpAvatarConversionReplayAnnotation(origin);
    ASS(!fullAnnotation.empty());
    env.options->set("proof_extra", "replay");
    splitter.recordAvatarConversion(converted);
    splitter.recordAvatarConversion(converted);
    ASS_EQ(Kernel::tptpAvatarConversionReplayAnnotation(origin), fullAnnotation);
    env.options->set("proof", "tptp_ac");
    definitions = Kernel::tptpAvatarConversionReplayDefinitions(origin);
    ASS_EQ(definitions.size(), 2);
    // ConstIterator reverses the input core; here its endpoints are identical.
    auto entry = [&](unsigned i, SAT::SATLiteral name, Unit* definition) {
      SAT::SATLiteral positive(name.var(), true);
      return "map(literal(f" + std::to_string(origin->number()) + ',' + std::to_string(i) + ")," +
        (name.positive() ? "positive(" : "negative(") +
        Saturation::Splitter::getFormulaStringFromLiteral(positive) + "),f" +
        std::to_string(definition->number()) + ')';
    };
    expected = "avatar_map([" + entry(0, eqName.opposite(), eqDefinition) + ',' +
      entry(1, neqName.opposite(), neqDefinition) + ',' + entry(2, eqName.opposite(), eqDefinition) + "])";
    // Printing must not rely on either the naming table or the live splitter.
    splitter.satNaming().reset();
  }
  ASS_EQ(Kernel::tptpAvatarConversionReplayAnnotation(origin), expected);
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream out;
  store->outputProof(out, origin);
  for (Unit* definition : definitions) {
    std::string prefix = "fof(f" + std::to_string(definition->number()) + ",definition,";
    ASS(out.str().find(prefix) != std::string::npos);
    ASS(out.str().find(prefix) < out.str().find("fof(f" + std::to_string(origin->number()) + ",axiom,"));
  }
  // Extra definitions are output-only dependencies, not parents of the axiom.
  ASS(!origin->getParents().hasNext());
  std::istringstream input(out.str());
  Parse::TPTP parser(input, "theory-conversion.tstp");
  parser.parse();
}

TEST_FUN(backward_subsumption_resolution_replays_all_solver_alternatives)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({~p(a), r(a), ~p(b), r(b)});
  auto side = clause({p(x), r(x)});
  for (unsigned removed : {0u, 2u}) {
    Stack<Lit> survivors;
    for (unsigned i = 0; i < main->length(); ++i) {
      if (i != removed) { survivors.push((*main)[i]); }
    }
    auto goal = clause(survivors,
        SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION, main, side));
    auto annotation = replay(goal);
    ASS(annotation.information);
    ASS_EQ(annotation.information->literalPositions[0].literalIndex, removed);
    ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(0), TermList(removed ? b : a));
    ac(goal, annotation, {});
  }
}

TEST_FUN(backward_subsumption_resolution_unit_replays_later_candidate)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto main = clause({q(a), ~p(a), ~p(b)});
  auto side = clause({p(x)});
  auto goal = clause({q(a), ~p(a)},
      SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION, main, side));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->substitutionForBanksSub[1].apply(0), TermList(b));
  ASS_EQ(annotation.information->literalPositions[0].literalIndex, 2);
  ac(goal, annotation, {});
}

TEST_FUN(subsumption_equality_resolution_replays_later_candidate)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_VAR(u, 3)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto main = clause({x.sort(sort) != y, p(y), z.sort(sort) != u, q(u)});
  auto goal = clause({x.sort(sort) != y, p(y), q(u)},
      SimplifyingInference1(InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION, main));
  auto annotation = replay(goal);
  ASS(annotation.information);
  ASS_EQ(annotation.information->literalPositions[0].literalIndex, 2);
  ASS_EQ(annotation.information->substitutionForBanksSub[0].apply(2), TermList(u));
  ac(goal, annotation, {});
}

TEST_FUN(unit_resulting_resolution_composes_nonground_parent_banks)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_FUNC(f, {sort}, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  DECL_PRED(r, {sort})
  auto main = clause({~p(x), ~q(x), r(f(x))});
  auto first = clause({p(y)});
  auto second = clause({q(z)});
  UnitList* parents = UnitList::cons(main, UnitList::cons(first, UnitList::cons(second, nullptr)));
  TermList v = TermList::var(9);
  auto goal = clause({r(f(v))}, GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, parents));
  auto annotation = replay(goal);
  ASS(annotation.information);
  const auto& banks = annotation.information->substitutionForBanksSub;
  ASS_EQ(banks[0].apply(0), v);
  ASS_EQ(banks[1].apply(1), v);
  ASS_EQ(banks[2].apply(2), v);
  ac(goal, annotation, {});
}

TEST_FUN(invalid_goals_and_disabled_replay_emit_no_substitution)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  DECL_PRED(q, {sort})
  auto left = clause({p(x)}), right = clause({~q(a)});
  auto goal = clause(Stack<Lit>(), GeneratingInference2(InferenceRule::EXTENSIONALITY_RESOLUTION, left, right));
  auto annotation = replay(goal);
  ASS(!annotation.information);
  ASS(renderedReplay(goal, annotation).empty());
  Shell::InferenceReplayer replayer;
  ASS(renderedReplay(goal, Shell::InferenceRecorder::inferenceReplayAnnotation(goal, replayer, false)).empty());
}
