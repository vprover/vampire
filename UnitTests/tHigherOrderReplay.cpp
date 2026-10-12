/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Inferences/HOL/FlexFlexSimplify.hpp"
#include "Inferences/HOL/CNFOnTheFly.hpp"
#include "Inferences/HOL/Cases.hpp"
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/HOL/CasesSimp.hpp"
#include "Inferences/HOL/Choice.hpp"
#include "Inferences/HOL/ImitateProject.hpp"
#include "Inferences/HOL/LeibnizEqualityElimination.hpp"
#include "Inferences/HOL/NegativeExtensionality.hpp"
#include "Inferences/HOL/PrimitiveInstantiation.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"
#include "Shell/Skolem.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/TPTPReplayProofPrinter.hpp"
#include "Shell/ACReconstruction.hpp"
#include "Shell/FunctionDefinition.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Shell/Options.hpp"

#include <sstream>
#include <type_traits>

using namespace Kernel;
using namespace Test;

static std::string printedProof(Unit* goal, const char* proof = "tptp", bool enableReplay = true)
{
  Problem problem;
  // Include the parents: an empty goal alone does not declare their sorts.
  UnitList* units = UnitList::singleton(goal);
  auto parents = goal->getParents();
  while (parents.hasNext()) { UnitList::push(parents.next(), units); }
  problem.addUnits(units);
  env.setMainProblem(&problem);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("proof", proof);
  env.options->set("replay", enableReplay ? "on" : "off");
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream out;
  store->outputProof(out, goal);
  return out.str();
}

static Shell::InferenceRecorder::InferenceReplayAnnotation replayed(Clause* goal)
{
  Problem problem;
  UnitList* units = UnitList::singleton(goal);
  auto parents = goal->getParents();
  while (parents.hasNext()) { UnitList::push(parents.next(), units); }
  problem.addUnits(units);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  Shell::InferenceReplayer replayer;
  replayer.makeInferenceEngine(OrderingSP(Ordering::create(problem, *env.options)));
  return Shell::InferenceRecorder::inferenceReplayAnnotation(goal, replayer, true);
}

template<class Engine>
static Clause* generated(Clause* parent, InferenceRule wanted)
{
  Problem problem;
  problem.addUnits(UnitList::singleton(parent));
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  MockedSaturationAlgorithm alg(problem, *env.options);
  auto engine = [&]() {
    if constexpr (std::is_constructible_v<Engine, Saturation::SaturationAlgorithm&>) {
      return Engine(alg);
    } else {
      return Engine();
    }
  }();
  auto clauses = engine.generateClauses(parent);
  while (clauses.hasNext()) {
    Clause* result = clauses.next();
    if (result->inference().rule() == wanted) { return result; }
  }
  ASSERTION_VIOLATION;
}

static unsigned count(const std::string& text, const std::string& pattern)
{
  unsigned result = 0;
  for (auto position = text.find(pattern); position != std::string::npos;
       position = text.find(pattern, position + 1)) {
    ++result;
  }
  return result;
}

TEST_FUN(occurrence_selector_visits_arguments_left_to_right_without_descending_into_matches)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_FUNC(f, {sort, sort}, sort)
  DECL_PRED(p, {sort, sort})
  Literal* literal = p(f(a, a), a);
  ASS_EQ(replaceOccurrence(literal, a, b, 0), (Literal*)p(f(b, a), a));
  ASS_EQ(replaceOccurrence(literal, a, b, 1), (Literal*)p(f(a, b), a));
  ASS_EQ(replaceOccurrence(literal, a, b, 2), (Literal*)p(f(a, a), b));
  ASS_EQ(replaceOccurrence(literal, a, b, 3), (Literal*)nullptr);
  // A match hides its descendants: `a` inside `f(a,a)` is not counted.
  Literal* nested = p(f(a, a), f(a, a));
  ASS_EQ(replaceOccurrence(nested, f(a, a), b, 1), (Literal*)p(f(a, a), b));
  ASS_EQ(replaceOccurrence(nested, f(a, a), b, 2), (Literal*)nullptr);
}

TEST_FUN(definition_unfolding_certifies_all_occurrences_or_selects_one)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {sort, sort})
  DECL_PRED(q, {sort})
  env.options->set("proof_extra", "replay");
  auto parent = clause({p(a, a), q(b)});
  auto definition = clause({a == b});

  auto all = clause({p(b, b), q(b)},
      NonspecificInference2(InferenceRule::DEFINITION_UNFOLDING, parent, definition));
  Shell::ACReconstruction::recordPreprocessingOrder(all);
  auto fp = "f" + std::to_string(parent->number());
  auto fd = "f" + std::to_string(definition->number());
  ASS_EQ(tptpDefinitionUnfoldingReplayAnnotation(all),
         "unifier([subs(" + fp + ",[]),subs(" + fd + ",[])]),rewritten_literal(literal(" + fp +
         ",0)),rewrite([equality(literal(" + fd + ",0)),from(a),to(b)])");

  auto single = clause({p(a, b), q(b)},
      NonspecificInference2(InferenceRule::DEFINITION_UNFOLDING, parent, definition));
  Shell::ACReconstruction::recordPreprocessingOrder(single);
  ASS(tptpDefinitionUnfoldingReplayAnnotation(single).find("from(a),to(b),occurrence(1)])") !=
      std::string::npos);
}

TEST_FUN(non_lower_word_rule_names_are_quoted)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  env.options->set("proof_extra", "off");
  auto axiom = clause({p(a)}, NonspecificInference0(UnitInputType::AXIOM,
                                                    InferenceRule::HILBERTS_CHOICE_INSTANCE));
  auto text = printedProof(axiom);
  ASS(text.find("['Hilbertian_choice_axiom_instance']") != std::string::npos);
}

#define HO_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  [[maybe_unused]] DECL_SORT_BOOL                  \
  DECL_VAR_SORTED(F, 0, arrow(srt, srt))           \
  DECL_VAR_SORTED(G, 1, arrow({srt, srt}, srt))    \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

TEST_FUN(flex_flex_closure_replays_a_checked_common_instance)
{
  HO_SYNTAX_SUGAR
  env.setHigherOrder(true);
  env.options->set("proof_extra", "replay");
  auto parent = clause({ap(F, a) != ap(ap(G, a), b)});
  auto empty = Inferences::FlexFlexSimplify().simplify(parent);
  ASS(empty != parent && empty->isEmpty());
  ASS(!env.proofExtra.find(empty));
  Shell::InferenceReplayer replayer;
  auto replay = Shell::InferenceRecorder::inferenceReplayAnnotation(empty, replayer, true);
  ASS(replay.information);
  const auto& subst = replay.information->substitutionForBanksSub[0];
  Literal* instance = SubstHelper::apply((*parent)[0], subst);
  ASS_EQ(HOL::reduce::betaNF(instance->termArg(0)), HOL::reduce::betaNF(instance->termArg(1)));

  auto text = printedProof(empty);
  ASS(text.find("inference('flex-flex_simplification',[unifier([subs(f" +
                std::to_string(parent->number()) + ",[") != std::string::npos);
  env.setHigherOrder(false);
}

TEST_FUN(builtin_axiom_symbols_are_introduced_once)
{
  HO_SYNTAX_SUGAR
  env.setHigherOrder(true);
  env.options->set("proof_extra", "replay");
  auto first = HOL::create::functionalExtensionalityAxiom();
  auto second = HOL::create::functionalExtensionalityAxiom();
  auto goal = clause({a == b}, GeneratingInference2(InferenceRule::RESOLUTION, first, second));
  auto text = printedProof(goal);
  auto diff = env.signature->getFunction(env.signature->getDiff())->name();
  ASS_EQ(count(text, "new_symbols(extensionality,[" + diff + "])"), 1u);
  ASS_EQ(count(text, "inference(functional_extensionality_axiom,["), 2u);
  ASS_EQ(count(text, "extensionality_axiom(" + diff + ",X2,X3)"), 2u);
  env.setHigherOrder(false);
}

TEST_FUN(imitation_and_projection_replay_without_search_time_certificates)
{
  HO_SYNTAX_SUGAR
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(ap(F, a) != a)});
  for (auto rule : {InferenceRule::IMITATION, InferenceRule::PROJECTION}) {
    auto goal = generated<Inferences::ImitateProject>(parent, rule);
    ASS(!env.proofExtra.find(goal));
    auto replay = replayed(goal);
    ASS(replay.information);
    ASS_EQ(replay.information->premises[0], parent);
    auto binding = replay.information->substitutionForBanksSub[0].apply(0);
    ASS(binding.isLambdaTerm());
    ASS(Kernel::formatTPTPReplayAnnotations(goal, replay).find("b(X0,$thf(") != std::string::npos);
  }
  env.setHigherOrder(false);
}

TEST_FUN(primitive_instantiation_replays_with_the_common_substitution_banks)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(P, 2, arrow(srt, Bool))
  DECL_CONST(pred, arrow(srt, Bool))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(ap(P, a) == ap(pred, a)), P == pred});
  auto goal = generated<Inferences::PrimitiveInstantiation>(parent, InferenceRule::PRIMITIVE_INSTANTIATION);
  ASS(!env.proofExtra.find(goal));
  auto replay = replayed(goal);
  ASS(replay.information);
  ASS(replay.information->substitutionForBanksSub[0].apply(2).isLambdaTerm());
  auto text = printedProof(goal);
  ASS(text.find("inference(primitive_instantiation,[unifier([subs(") != std::string::npos);
  ASS(printedProof(goal, "tptp", false).find("unifier(") == std::string::npos);
  env.setHigherOrder(false);
}

TEST_FUN(leibniz_elimination_replays_the_selected_predicate)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(P, 2, arrow(srt, Bool))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({ap(P, a) == HOL::create::top(), ap(P, b) == HOL::create::bottom()});
  auto goal = generated<Inferences::LeibnizEqualityElimination>(parent, InferenceRule::LEIBNIZ_ELIMINATION);
  auto replay = replayed(goal);
  ASS(replay.information);
  ASS(replay.information->substitutionForBanksSub[0].apply(2) != TermList::var(2));
  ASS(!env.proofExtra.find(goal));
  env.setHigherOrder(false);
}

TEST_FUN(negative_extensionality_reuses_the_goal_witness_and_renames_dependencies)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(H, 1, arrow(srt, srt))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(F != H)});
  auto original = generated<Inferences::NegativeExtensionality>(parent, InferenceRule::NEGATIVE_EXTENSIONALITY);
  Substitution rename;
  rename.bind(0, TermList::var(7));
  rename.bind(1, TermList::var(8));
  auto goal = clause({SubstHelper::apply((*original)[0], rename)},
      GeneratingInference1(InferenceRule::NEGATIVE_EXTENSIONALITY, parent));
  unsigned symbols = env.signature->functions();
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->witness);
  ASS_EQ(env.signature->functions(), symbols);
  ASS_EQ(replay.information->substitutionForBanksSub[0].apply(0), TermList::var(7));
  ASS_EQ(replay.information->substitutionForBanksSub[0].apply(1), TermList::var(8));
  const auto& witness = *replay.information->witness;
  ASS_EQ(witness.literalIndex, 0u);
  ASS_EQ(witness.dependencies.size(), 2u);
  for (TermList dependency : witness.dependencies) {
    ASS(dependency == TermList::var(7) || dependency == TermList::var(8));
  }
  auto text = printedProof(goal);
  ASS(text.find("extensionality_witness(literal(f" + std::to_string(parent->number()) + ",0)") != std::string::npos);
  ASS(!env.proofExtra.find(goal));
  env.setHigherOrder(false);
}

TEST_FUN(sigma_clausification_replays_a_fresh_witness_without_allocating_a_symbol)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(P, 2, arrow(srt, Bool))
  DECL_SIGMA_PROXY
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  env.options->set("cnf_on_the_fly", "lazy_gen");
  auto parent = clause({ap(sigmaP(srt), P) == HOL::create::top()});
  auto goal = generated<Inferences::LazyClausificationGIE>(parent, InferenceRule::SIGMA_PROXY_CLAUSIFICATION);
  unsigned symbols = env.signature->functions();
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->witness);
  ASS_EQ(env.signature->functions(), symbols);
  ASS_EQ(replay.information->witness->kind, Shell::InferenceRecorder::InferenceInformation::WitnessKind::QUANTIFIER);
  ASS(!env.proofExtra.find(goal));
  env.setHigherOrder(false);
}

TEST_FUN(sigma_replay_preserves_instantiated_dependencies_of_a_reused_witness)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(x, 2, srt)
  DECL_CONST(pred, arrow({srt, srt}, Bool))
  DECL_CONST(f, arrow(srt, srt))
  DECL_SIGMA_PROXY
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto skolem = Shell::Skolem::addSkolemFunction(0, TermStack(), arrow(srt, srt))->number();
  auto witness = ap(TermSugar(TermList(Term::createConstant(skolem))), ap(f, x));
  auto predicate = ap(pred, x);
  auto parent = clause({ap(sigmaP(srt), predicate) == HOL::create::top(), a == b});
  auto goal = clause({ap(predicate, witness) == HOL::create::top(), a == b},
      GeneratingInference1(InferenceRule::SIGMA_PROXY_CLAUSIFICATION, parent));
  unsigned symbols = env.signature->functions();
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->witness);
  ASS_EQ(replay.information->witness->symbol, skolem);
  ASS_EQ(replay.information->witness->dependencies.size(), 1u);
  ASS_EQ(replay.information->witness->dependencies[0], TermList(ap(f, x)));
  ASS_EQ(env.signature->functions(), symbols);
  env.setHigherOrder(false);
}

TEST_FUN(heuristic_instantiation_replays_the_original_quantifier_engine)
{
  HO_SYNTAX_SUGAR
  DECL_CONST(pred, arrow(srt, Bool))
  DECL_PI_PROXY
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  env.signature->addInstantiation(a);
  auto parent = clause({ap(piP(srt), pred) == HOL::create::top()});
  auto goal = clause({ap(pred, a) == HOL::create::top()},
      GeneratingInference1(InferenceRule::HEURISTIC_INSTANTIATION, parent));
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->quantifierInstance);
  ASS_EQ(replay.information->quantifierInstance->term, TermList(a));
  ASS_EQ(replay.information->quantifierInstance->literalIndex, 0u);
  ASS(printedProof(goal).find("quantifier_instance(literal(") != std::string::npos);
  env.setHigherOrder(false);
}

TEST_FUN(boolean_case_replay_selects_the_matching_candidate_and_literal_order)
{
  HO_SYNTAX_SUGAR
  DECL_CONST(boolTerm, Bool)
  DECL_CONST(f, arrow(Bool, srt))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({ap(f, boolTerm) == a, a != b});
  auto goal = clause({a != b, ap(f, HOL::create::bottom()) == a, boolTerm == HOL::create::top()},
      SimplifyingInference1(InferenceRule::CASES_SIMP, parent));
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->booleanCase);
  ASS(!replay.information->booleanCase->value);
  ASS_EQ(replay.information->booleanCase->literalIndex, 0u);
  ASS_EQ(replay.information->booleanCase->term, TermList(boolTerm));
  ASS(printedProof(goal, "tstp-ac").find("inference(associativity_commutativity") != std::string::npos);
  env.setHigherOrder(false);
}

TEST_FUN(parentless_choice_axioms_replay_without_search_time_certificates)
{
  HO_SYNTAX_SUGAR
  DECL_CONST(choice, arrow(arrow(srt, Bool), srt))
  DECL_VAR_SORTED(P, 2, arrow(srt, Bool))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto builtin = HOL::create::choiceAxiom();
  auto replay = replayed(builtin);
  ASS(replay.information && replay.information->axiom);
  ASS(replay.information->premises.empty());
  ASS_EQ(replay.information->axiom->kind, Shell::InferenceRecorder::InferenceInformation::AxiomKind::CHOICE);
  env.signature->addChoiceOperator(TermList(choice).term()->functor());
  auto goal = Inferences::Choice::createChoiceAxiom(choice, P);
  unsigned symbols = env.signature->functions();
  auto custom = replayed(goal);
  ASS(custom.information && custom.information->axiom);
  ASS_EQ(custom.information->axiom->symbol, TermList(choice).term()->functor());
  ASS_EQ(env.signature->functions(), symbols);
  ASS(!env.proofExtra.find(goal));
  auto text = printedProof(goal);
  ASS(text.find("choice_axiom(") != std::string::npos);
  ASS(text.find("new_symbols(choice,") == std::string::npos);
  env.setHigherOrder(false);
}

TEST_FUN(replay_rejects_a_higher_order_candidate_with_a_different_conclusion)
{
  HO_SYNTAX_SUGAR
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(ap(F, a) != a)});
  auto goal = clause({a == b}, GeneratingInference1(InferenceRule::PROJECTION, parent));
  ASS(!replayed(goal).information);
  ASS(!env.proofExtra.find(goal));
  env.setHigherOrder(false);
}

TEST_FUN(fool_paramodulation_replays_through_the_matching_engine_in_both_fragments)
{
  HO_SYNTAX_SUGAR
  DECL_CONST(boolTerm, Bool)
  DECL_CONST(f, arrow(Bool, srt))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(ap(f, boolTerm) == a)});
  auto goal = generated<Inferences::Cases>(parent, InferenceRule::FOOL_PARAMODULATION);
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->booleanCase);
  ASS_EQ(replay.information->booleanCase->term, TermList(boolTerm));
  env.setHigherOrder(false);
  DECL_FUNC(firstOrder, {Bool}, srt)
  auto firstOrderParent = clause({selected(firstOrder(boolTerm) == a)});
  auto firstOrderGoal = generated<Inferences::FOOLParamodulation>(firstOrderParent, InferenceRule::FOOL_PARAMODULATION);
  auto firstOrderReplay = replayed(firstOrderGoal);
  ASS(firstOrderReplay.information && firstOrderReplay.information->booleanCase);
  ASS_EQ(firstOrderReplay.information->booleanCase->term, TermList(boolTerm));
}

TEST_FUN(negative_extensionality_replay_rejects_a_witness_with_missing_dependencies)
{
  HO_SYNTAX_SUGAR
  DECL_VAR_SORTED(H, 1, arrow(srt, srt))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(F != H)});
  auto skolem = Shell::Skolem::addSkolemFunction(0, TermStack(), srt)->number();
  auto witness = TermSugar(TermList(Term::createConstant(skolem)));
  auto goal = clause({ap(F, witness) != ap(H, witness)},
      GeneratingInference1(InferenceRule::NEGATIVE_EXTENSIONALITY, parent));
  unsigned symbols = env.signature->functions();
  ASS(!replayed(goal).information);
  ASS_EQ(env.signature->functions(), symbols);
  env.setHigherOrder(false);
}

TEST_FUN(polymorphic_witness_replay_preserves_type_arguments_and_goal_variable_names)
{
  DECL_SORT_VAR(A, 0)
  DECL_VAR_SORTED(F, 1, arrow(A, A))
  DECL_VAR_SORTED(G, 2, arrow(A, A))
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto parent = clause({selected(F != G)});
  auto original = generated<Inferences::NegativeExtensionality>(parent, InferenceRule::NEGATIVE_EXTENSIONALITY);
  Substitution rename;
  rename.bind(0, TermList::var(10));
  rename.bind(1, TermList::var(11));
  rename.bind(2, TermList::var(12));
  auto goal = clause({SubstHelper::apply((*original)[0], rename)},
      GeneratingInference1(InferenceRule::NEGATIVE_EXTENSIONALITY, parent));
  unsigned symbols = env.signature->functions();
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->witness);
  ASS_EQ(replay.information->substitutionForBanksSub[0].apply(0), TermList::var(10));
  ASS_EQ(env.signature->functions(), symbols);
  env.setHigherOrder(false);
}

TEST_FUN(parentless_axiom_replay_preserves_renaming_and_natural_literal_order)
{
  HO_SYNTAX_SUGAR
  env.setHigherOrder(true);
  env.options->set("proof_extra", "off");
  auto original = HOL::create::functionalExtensionalityAxiom();
  Substitution rename;
  for (unsigned variable = 0; variable < 4; ++variable) {
    rename.bind(variable, TermList::var(variable + 10));
  }
  auto goal = clause({SubstHelper::apply((*original)[1], rename), SubstHelper::apply((*original)[0], rename)},
      TheoryAxiom(InferenceRule::FUNCTIONAL_EXTENSIONALITY_AXIOM));
  auto replay = replayed(goal);
  ASS(replay.information && replay.information->axiom);
  ASS_EQ(replay.information->axiom->arguments[0], TermList::var(12));
  ASS_EQ(replay.information->axiom->arguments[1], TermList::var(13));
  auto text = printedProof(goal, "tstp-ac");
  ASS(text.find("inference(associativity_commutativity") != std::string::npos);
  ASS(text.find(",X12,X13)") != std::string::npos);
  env.setHigherOrder(false);
}
