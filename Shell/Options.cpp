/**
 * @file Options.cpp
 * Implements Vampire options.
 *
 * @since 06/06/2001 Manchester, completely rewritten
 */

// Visual does not know the round function
#include <cmath>
#include <sstream>
#include <cstring> 
#include <fstream>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"
#include "Debug/Assertion.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/NameArray.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/System.hpp"

#include "Parse/TPTP.hpp"

#include "Kernel/Problem.hpp"

#include "Options.hpp"
#include "Property.hpp"

using namespace Lib;
using namespace Shell;

/**
 * Class to hide various data used by class Options, mostly name arrays.
 * @since 21/04/2005 Manchester
 */
class Options::Constants {
public:
  static const char* _optionNames[];
  static const char* _shortNames[];
  static const char* _statisticsValues[];
  static const char* _condensationValues[];
  static const char* _demodulationValues[];
  static const char* _subsumptionValues[];
  static const char* _urResolutionValues[];
//  static const char* _splittingModeValues[];
  static const char* _fdeValues[];
  static const char* _lcmValues[];
  static const char* _satSolverValues[];
  static const char* _satAlgValues[];
  static const char* _equalityProxyValues[];
  static const char* _extensionalityResolutionValues[];
  static const char* _inputSyntaxValues[];
  static const char* _modeValues[];
  static const char* _ruleActivityValues[];
  static const char* _questionAnsweringValues[];
  static const char* _inliningModeValues[];
  static const char* _interpolantModeValues[];
  static const char* _symbolPrecedenceValues[];
  static const char* _tcValues[];
  static const char* _sineSelectionValues[];
  static const char* _proofValues[];
  static const char* _satRestartStrategyValues[];
  static const char* _satVarSelectorValues[];
  static const char* _nicenessOptionValues[];
  static const char* _satClauseDisposerValues[];
  static const char* _sosValues[];
  static const char* _sSplittingComponentSweepingValues[];
  static const char* _sSplittingAddComplementaryValues[];
  static const char* _sSplittingNonsplittableComponentsValues[];
  static const char* _predicateEquivalenceDiscoveryModeValues[];
  static const char* _bpAssignmentSelectorValues[];
  static const char* _bpVariableSelectorValues[];
  static const char* _bpConflictSelectorValues[];
  static const char* _bpAlmostHalfBoundingRemovalValues[];
  static int shortNameIndexes[];

  static NameArray optionNames;
  static NameArray shortNames;
  static NameArray statisticsValues;
  static NameArray condensationValues;
  static NameArray demodulationValues;
  static NameArray subsumptionValues;
  static NameArray urResolutionValues;
//  static NameArray splittingModeValues;
  static NameArray fdeValues;
  static NameArray lcmValues;
  static NameArray satSolverValues;
  static NameArray satAlgValues;
  static NameArray equalityProxyValues;
  static NameArray extensionalityResolutionValues;
  static NameArray inputSyntaxValues;
  static NameArray modeValues;
  static NameArray ruleActivityValues;
  static NameArray questionAnsweringValues;
  static NameArray inliningModeValues;
  static NameArray interpolantModeValues;
  static NameArray symbolPrecedenceValues;
  static NameArray tcValues;
  static NameArray sineSelectionValues;
  static NameArray proofValues;
  static NameArray satRestartStrategyValues;
  static NameArray satVarSelectorValues;
  static NameArray nicenessOptionValues;
  static NameArray satClauseDisposerValues;
  static NameArray sosValues;
  static NameArray sSplittingComponentSweepingValues;
  static NameArray sSplittingAddComplementaryValues;
  static NameArray sSplittingNonsplittableComponentsValues;
  static NameArray predicateEquivalenceDiscoveryModeValues;
  static NameArray bpAssignmentSelectorValues;
  static NameArray bpVariableSelectorValues;
  static NameArray bpConflictSelectorValues;
  static NameArray bpAlmostHalfBoundingRemovalValues;
}; // class Options::Constants


/** Names for all options */
const char* Options::Constants::_optionNames[] = {
  "age_weight_ratio",
  "aig_bdd_sweeping",
  "aig_conditional_rewriting",
  "aig_definition_introduction",
  "aig_definition_introduction_threshold",
  "aig_formula_sharing",
  "aig_inliner",
  "arity_check",

  "backward_demodulation",
  "backward_subsumption",
  "backward_subsumption_resolution",
  "bfnt",
  "binary_resolution",
  "bp_add_collapsing_inequalities",
  "bp_allowed_fm_balance",
  "bp_almost_half_bounding_removal",
  "bp_assignment_selector",
  "bp_bound_improvement_limit",
  "bp_conflict_selector",
  "bp_conservative_assignment_selection",
  "bp_fm_elimination",
  "bp_max_prop_length",
  "bp_propagate_after_conflict",
  "bp_start_with_precise",
  "bp_start_with_rational",
  "bp_variable_selector",

  "color_unblocking",
  "condensation",

  "decode",
  "demodulation_redundancy_check",
  "distinct_processor",

  "epr_preserving_naming",
  "epr_preserving_skolemization",
  "epr_restoring_inlining",
  "equality_propagation",
  "equality_proxy",
  "equality_resolution_with_deletion",
  
  "extensionality_allow_pos_eq",
  "extensionality_max_length",
  "extensionality_resolution",

  "flatten_top_level_conjunctions",
  "forbidden_options",
  "forced_options",
  "forward_demodulation",
  "forward_literal_rewriting",
  "forward_subsumption",
  "forward_subsumption_resolution",
  "function_definition_elimination",
  "function_number",

  "general_splitting",
  "global_subsumption",

  "horn_revealing",
  "hyper_superposition",

  "ignore_missing",
  "include",
  "increased_numeral_weight",
  "inequality_splitting",
  "input_file",
  "input_syntax",
  "inst_gen_big_restart_ratio",
  "inst_gen_inprocessing",
  "inst_gen_passive_reactivation",
  "inst_gen_resolution_ratio",
  "inst_gen_restart_period",
  "inst_gen_restart_period_quotient",
  "inst_gen_selection",
  "inst_gen_with_resolution",
  "interpreted_simplification",

  "latex_output",
  "lingva_additional_invariants",

  "literal_comparison_mode",
  "log_file",
  "lrs_first_time_check",
  "lrs_weight_limit_only",

  "max_active",
  "max_answers",
  "max_inference_depth",
  "max_passive",
  "max_weight",
  "memory_limit",
  "mode",

  "multi_proof_attempt_concurrent",
  "multi_proof_attempt_priority",

  "name_prefix",
  "naming",
  "niceness_option",
  "nongoal_weight_coefficient",
  "nonliterals_in_clause_weight",
  "normalize",

  "output_axiom_names",

  "predicate_definition_inlining",
  "predicate_definition_merging",
  "predicate_equivalence_discovery",
  "predicate_equivalence_discovery_add_implications",
  "predicate_equivalence_discovery_random_simulation",
  "predicate_equivalence_discovery_sat_conflict_limit",
  "predicate_index_introduction",
  "print_clausifier_premises",
  "problem_name",
  "proof",
  "proof_checking",
  "protected_prefix",

  "question_answering",

  "random_seed",
  "row_variable_max_length",

  "sat_clause_activity_decay",
  "sat_clause_disposer",
  "sat_learnt_minimization",
  "sat_learnt_subsumption_resolution",

  /** Lingeling options for incremental use and similar models generation*/
  "sat_lingeling_incremental",
  "sat_lingeling_similar_models",

  "sat_restart_fixed_count",
  "sat_restart_geometric_increase",
  "sat_restart_geometric_init",
  "sat_restart_luby_factor",
  "sat_restart_minisat_increase",
  "sat_restart_minisat_init",
  "sat_restart_strategy",
  "sat_solver",

  "sat_var_activity_decay",
  "sat_var_selector",
  "saturation_algorithm",
  "selection",
  "show_active",
  "show_blocked",
  "show_definitions",
  "show_interpolant",
  "show_new",
  "show_new_propositional",
  "show_nonconstant_skolem_function_trace",
  "show_options",
  "show_passive",
  "show_preprocessing",
  "show_skolemisations",
  "show_symbol_elimination",
  "show_theory_axioms",
  "simulated_time_limit",
  "sine_depth",
  "sine_generality_threshold",
  "sine_selection",
  "sine_tolerance",
  "smtlib_consider_ints_real",
  "smtlib_flet_as_definition",
  "smtlib_introduce_aig_names",
  "sos",
 // "split_add_ground_negation",
  "split_at_activation",
 // "split_goal_only",
 // "split_input_only",
 // "split_positive",
  "splitting",
  "ssplitting_add_complementary",
  "ssplitting_component_sweeping",
  "ssplitting_congruence_closure",
  "ssplitting_eager_removal",
  "ssplitting_flush_period",
  "ssplitting_flush_quotient",
  "ssplitting_nonsplittable_components",
  "statistics",
  "superposition_from_variables",
  "symbol_precedence",

  "tabulation_bw_rule_subsumption_resolution_by_lemmas",
  "tabulation_fw_rule_subsumption_resolution_by_lemmas",
  "tabulation_goal_awr",
  "tabulation_goal_lemma_ratio",
  "tabulation_instantiate_producing_rules",
  "tabulation_lemma_awr",
  "test_id",
  "thanks",
  "theory_axioms",
  "time_limit",
  "time_limit_local",
  "time_statistics",
  "trivial_predicate_removal",

  "unit_resulting_resolution",
  "unused_predicate_definition_removal",
  "use_dismatching",
  "weight_increment",
  "while_number",

  "xml_output"};

/** Names for all options */
NameArray Options::Constants::optionNames(_optionNames,
					  sizeof(_optionNames)/sizeof(char*));

const char* Options::Constants::_shortNames[] = {
  "awr",

  "bd",
  "bfnt",
  "br",
  "bs",
  "bsr",

  "cond",

  "drc",

  "ep",
  "er",
  "erd",

  "fd",
  "fde",
  "flr",
  "fs",
  "fsr",

  "gs",
  "gsp",

  "igbrr",
  "igrp",
  "igrpq",
  "igrr",
  "igs",
  "igwr",
  "ins",

  "lcm",

  "m",

  "nicw",
  "nm",
  "no",
  "nwc",

  "p",

  "s",
  "sa",
  "sac",
  "sas",
  //"sagn",
  "sd",
  "sfv",
  //"sgo",
  "sgt",
  //"sio",
  "sos",
  "sp",
  "spl",
  //"spo",
  "ss",
  "ssac",
  "sscc",
  "sser",
  "ssfp",
  "ssfq",
  "ssnc",
  "st",
  "stl",
  "svs",

  "t",
  "tbsr",
  "tfsr",
  "tgawr",
  "tglr",
  "tipr",
  "tl",
  "tlawr",

  "updr",
  "urr"
};

/** Short names for all options */
NameArray Options::Constants::shortNames(_shortNames,
					  sizeof(_shortNames)/sizeof(char*));

int Options::Constants::shortNameIndexes[] = {
  AGE_WEIGHT_RATIO,

  BACKWARD_DEMODULATION,
  BFNT,
  BINARY_RESOLUTION,
  BACKWARD_SUBSUMPTION,
  BACKWARD_SUBSUMPTION_RESOLUTION,

  CONDENSATION,

  DEMODULATION_REDUNDANCY_CHECK,

  EQUALITY_PROXY,
  EXTENSIONALITY_RESOLUTION,
  EQUALITY_RESOLUTION_WITH_DELETION,

  FORWARD_DEMODULATION,
  FUNCTION_DEFINITION_ELIMINATION,
  FORWARD_LITERAL_REWRITING,
  FORWARD_SUBSUMPTION,
  FORWARD_SUBSUMPTION_RESOLUTION,

  GLOBAL_SUBSUMPTION,
  GENERAL_SPLITTING,

  INST_GEN_BIG_RESTART_RATIO,
  INST_GEN_RESTART_PERIOD,
  INST_GEN_RESTART_PERIOD_QUOTIENT,
  INST_GEN_RESOLUTION_RATIO,
  INST_GEN_SELECTION,
  INST_GEN_WITH_RESOLUTION,
  INEQUALITY_SPLITTING,

  LITERAL_COMPARISON_MODE,

  MEMORY_LIMIT,

  NONLITERALS_IN_CLAUSE_WEIGHT,
  NAMING,
  NICENESS_OPTION,
  NONGOAL_WEIGHT_COEFFICIENT,

  PROOF,

  SELECTION,
  SATURATION_ALGORITHM,
  SPLIT_AT_ACTIVATION,
  SAT_SOLVER,
  //SPLIT_ADD_GROUND_NEGATION,
  SINE_DEPTH,
  SUPERPOSITION_FROM_VARIABLES,
  //SPLIT_GOAL_ONLY,
  SINE_GENERALITY_THRESHOLD,
  //SPLIT_INPUT_ONLY,
  SOS,
  SYMBOL_PRECEDENCE,
  SPLITTING,
  //SPLIT_POSITIVE,
  SINE_SELECTION,

  SSPLITTING_ADD_COMPLEMENTARY,
  SSPLITTING_CONGRUENCE_CLOSURE,
  SSPLITTING_EAGER_REMOVAL,
  SSPLITTING_FLUSH_PERIOD,
  SSPLITTING_FLUSH_QUOTIENT,
  SSPLITTING_NONSPLITTABLE_COMPONENTS,
  SINE_TOLERANCE,
  SIMULATED_TIME_LIMIT,

  SAT_VAR_SELECTOR,

  TIME_LIMIT,
  TABULATION_BW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS,
  TABULATION_FW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS,
  TABULATION_GOAL_AWR,
  TABULATION_GOAL_LEMMA_RATIO,
  TABULATION_INSTANTIATE_PRODUCING_RULES,
  TIME_LIMIT_LOCAL,
  TABULATION_LEMMA_AWR,

  UNUSED_PREDICATE_DEFINITION_REMOVAL,
  UNIT_RESULTING_RESOLUTION
};

const char* Options::Constants::_statisticsValues[] = {
  "brief",
  "full",
  "none"};
NameArray Options::Constants::statisticsValues(_statisticsValues,
					       sizeof(_statisticsValues)/sizeof(char*));

const char* Options::Constants::_condensationValues[] = {
  "fast",
  "off",
  "on"};
NameArray Options::Constants::condensationValues(_condensationValues,
						 sizeof(_condensationValues)/sizeof(char*));

const char* Options::Constants::_demodulationValues[] = {
  "all",
  "off",
  "preordered"};
NameArray Options::Constants::demodulationValues(_demodulationValues,
						 sizeof(_demodulationValues)/sizeof(char*));

const char* Options::Constants::_subsumptionValues[] = {
  "off",
  "on",
  "unit_only"};
NameArray Options::Constants::subsumptionValues(_subsumptionValues,
						 sizeof(_subsumptionValues)/sizeof(char*));

const char* Options::Constants::_urResolutionValues[] = {
  "ec_only",
  "off",
  "on"};
NameArray Options::Constants::urResolutionValues(_urResolutionValues,
						 sizeof(_urResolutionValues)/sizeof(char*));

//const char* Options::Constants::_splittingModeValues[] = {
//  "input",
//  "off",
//  "sat"};
//NameArray Options::Constants::splittingModeValues(_splittingModeValues,
//					sizeof(_splittingModeValues)/sizeof(char*));

const char* Options::Constants::_fdeValues[] = {
  "all",
  "none",
  "unused"};
NameArray Options::Constants::fdeValues(_fdeValues,
					sizeof(_fdeValues)/sizeof(char*));

const char* Options::Constants::_lcmValues[] = {
  "predicate",
  "reverse",
  "standard"
};
NameArray Options::Constants::lcmValues(_lcmValues,
					sizeof(_lcmValues)/sizeof(char*));

const char* Options::Constants::_satSolverValues[] = {
  "buf_lingeling",
  "buf_minisat",
  "buf_vampire",
  "lingeling",
  "minisat",
  "vampire"    
};
NameArray Options::Constants::satSolverValues(_satSolverValues,
                                              sizeof(_satSolverValues)/sizeof(char*));


const char* Options::Constants::_satAlgValues[] = {
  "discount",
  "inst_gen",
  "lrs",
  "otter",
  "tabulation"};
NameArray Options::Constants::satAlgValues(_satAlgValues,
					   sizeof(_satAlgValues)/sizeof(char*));

const char* Options::Constants::_equalityProxyValues[] = {
  "R",
  "RS",
  "RST",
  "RSTC",
  "off",
  "on"};
NameArray Options::Constants::equalityProxyValues(_equalityProxyValues,
						  sizeof(_equalityProxyValues)/sizeof(char*));

const char* Options::Constants::_extensionalityResolutionValues[] = {
  "filter",
  "known",
  "off"};
NameArray Options::Constants::extensionalityResolutionValues(_extensionalityResolutionValues,
						  sizeof(_extensionalityResolutionValues)/sizeof(char*));

const char* Options::Constants::_ruleActivityValues[] = {
  "input_only",
  "off",
  "on"};
NameArray Options::Constants::ruleActivityValues(_ruleActivityValues,
					      sizeof(_ruleActivityValues)/sizeof(char*));

const char* Options::Constants::_questionAnsweringValues[] = {
  "answer_literal",
  "from_proof",
  "off"};
NameArray Options::Constants::questionAnsweringValues(_questionAnsweringValues,
					      sizeof(_questionAnsweringValues)/sizeof(char*));

const char* Options::Constants::_inliningModeValues[] = {
  "axioms_only",
  "non_growing",
  "off",
  "on"};
NameArray Options::Constants::inliningModeValues(_inliningModeValues,
					      sizeof(_inliningModeValues)/sizeof(char*));

const char* Options::Constants::_interpolantModeValues[] = {
  "minimized",
  "off",
  "on"};
NameArray Options::Constants::interpolantModeValues(_interpolantModeValues,
					      sizeof(_interpolantModeValues)/sizeof(char*));

const char* Options::Constants::_symbolPrecedenceValues[] = {
  "arity",
  "occurrence",
  "reverse_arity"};
NameArray Options::Constants::symbolPrecedenceValues(_symbolPrecedenceValues,
						     sizeof(_symbolPrecedenceValues)/sizeof(char*));

const char* Options::Constants::_tcValues[] = {
  "full",
  "none",
  "only_nonvariables"};
NameArray Options::Constants::tcValues(_tcValues,
				       sizeof(_tcValues)/sizeof(char*));

const char* Options::Constants::_inputSyntaxValues[] = {
  "simplify",
  "smtlib",
  "smtlib2",
  "tptp",
  "xhuman",
  "xmps", 
  "xnetlib"
};
NameArray Options::Constants::inputSyntaxValues(_inputSyntaxValues,
						sizeof(_inputSyntaxValues)/sizeof(char*));

const char* Options::Constants::_modeValues[] = {
  "axiom_selection",
  "bpa", 
  "casc",
  "casc_epr",
  "casc_ltb",
  "casc_multi",
  "casc_mzr",
  "casc_sat",
  "clausify",
  "consequence_elimination",
  "grounding",
  "ltb_build",
  "ltb_solve",
  "output",
  "preprocess",
  "profile",
  "program_analysis",
  //runs the sat solver from vampire
  //Added for development reasons, Ioan Oct. 2013
  "sat_solver",

  "spider",
  "vampire"
};
NameArray Options::Constants::modeValues(_modeValues,
					 sizeof(_modeValues)/sizeof(char*));

/** Possible values for --sine_selection */
const char* Options::Constants::_sineSelectionValues[] = {
  "axioms",
  "included",
  "off"};
NameArray Options::Constants::sineSelectionValues(_sineSelectionValues,
					  sizeof(_sineSelectionValues)/sizeof(char*));

/** Possible values for --proof */
const char* Options::Constants::_proofValues[] = {
  "off",
  "on",
  "proofcheck",
  "tptp"};
NameArray Options::Constants::proofValues(_proofValues,
					  sizeof(_proofValues)/sizeof(char*));

const char* Options::Constants::_satRestartStrategyValues[] = {
  "fixed",
  "geometric",
  "luby",
  "minisat"};
NameArray Options::Constants::satRestartStrategyValues(_satRestartStrategyValues,
					  sizeof(_satRestartStrategyValues)/sizeof(char*));

const char* Options::Constants::_satVarSelectorValues[] = {
  "active",
  "niceness",
  "recently_learnt"};
NameArray Options::Constants::satVarSelectorValues(_satVarSelectorValues,
					  sizeof(_satVarSelectorValues)/sizeof(char*));

const char* Options::Constants::_nicenessOptionValues[] = {
  "average",
  "none",
  "sum",
  "top"
  };
NameArray Options::Constants::nicenessOptionValues(_nicenessOptionValues,
					  sizeof(_nicenessOptionValues)/sizeof(char*));

const char* Options::Constants::_satClauseDisposerValues[] = {
  "growing",
  "minisat"};
NameArray Options::Constants::satClauseDisposerValues(_satClauseDisposerValues,
					  sizeof(_satClauseDisposerValues)/sizeof(char*));

const char* Options::Constants::_sosValues[] = {
  "all",
  "off",
  "on"};
NameArray Options::Constants::sosValues(_sosValues,
					sizeof(_sosValues)/sizeof(char*));

const char* Options::Constants::_sSplittingComponentSweepingValues[] = {
  "all",
  "iterated",
  "none",
  "only_new"};
NameArray Options::Constants::sSplittingComponentSweepingValues(_sSplittingComponentSweepingValues,
					  sizeof(_sSplittingComponentSweepingValues)/sizeof(char*));

const char* Options::Constants::_sSplittingAddComplementaryValues[] = {
  "ground",
  "none"};
NameArray Options::Constants::sSplittingAddComplementaryValues(_sSplittingAddComplementaryValues,
					  sizeof(_sSplittingAddComplementaryValues)/sizeof(char*));

const char* Options::Constants::_sSplittingNonsplittableComponentsValues[] = {
  "all",
  "all_dependent",
  "known",
  "none"};
NameArray Options::Constants::sSplittingNonsplittableComponentsValues(_sSplittingNonsplittableComponentsValues,
					  sizeof(_sSplittingNonsplittableComponentsValues)/sizeof(char*));

const char* Options::Constants::_predicateEquivalenceDiscoveryModeValues[] = {
  "all_atoms",
  "all_formulas",
  "definitions",
  "off",
  "on"};

NameArray Options::Constants::predicateEquivalenceDiscoveryModeValues(_predicateEquivalenceDiscoveryModeValues,
								      sizeof(_predicateEquivalenceDiscoveryModeValues)/sizeof(char*));

const char* Options::Constants::_bpAssignmentSelectorValues[] = {
  "alternating",
  "bmp",
  "lower_bound",
  "middle",
  "random",
  "rational",
  "smallest",
  "tight",
  "tightish",
  "upper_bound"};

NameArray Options::Constants::bpAssignmentSelectorValues(_bpAssignmentSelectorValues,
							 sizeof(_bpAssignmentSelectorValues)/sizeof(char*));

const char* Options::Constants::_bpVariableSelectorValues[] = {
  "conflicting",
  "conflicting_and_collapsing",
  "first",
  "look_ahead",
  "random",
  "recent_collapsing",
  "recent_conflicting",
  "tightest_bound"
};

NameArray Options::Constants::bpVariableSelectorValues(_bpVariableSelectorValues,
						       sizeof(_bpVariableSelectorValues)/sizeof(char*));

const char* Options::Constants::_bpConflictSelectorValues[] = {
  "least_recent",
  "most_recent",
  "shortest"
};
NameArray Options::Constants::bpConflictSelectorValues(_bpConflictSelectorValues,
						       sizeof(_bpConflictSelectorValues)/sizeof(char*));

const char* Options::Constants::_bpAlmostHalfBoundingRemovalValues[] = {
  "bounds_on",
  "off",
  "on"
};

NameArray Options::Constants::bpAlmostHalfBoundingRemovalValues(_bpAlmostHalfBoundingRemovalValues,
								sizeof(_bpAlmostHalfBoundingRemovalValues)/sizeof(char*));


bool Options::_ssplittingEagerRemoval = true;

/**
 * Initialize options to the default values.
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()
  :
  _ageRatio(1),

  _aigBddSweeping(false),
  _aigConditionalRewriting(false),
  _aigDefinitionIntroduction(false),
  _aigDefinitionIntroductionThreshold(4),
  _aigFormulaSharing(false),
  _aigInliner(false),
  _arityCheck(false),

  _backjumpTargetIsDecisionPoint(true),
  _backwardDemodulation(DEMODULATION_ALL),
  _backwardSubsumption(SUBSUMPTION_ON),
  _backwardSubsumptionResolution(SUBSUMPTION_OFF),
  _bfnt(false),
  _binaryResolution(true),
  _bpAllowedFMBalance(0),
  _bpAlmostHalfBoundingRemoval(AHR_ON),
  _bpAssignmentSelector(ASG_RANDOM),
  _bpCollapsingPropagation(false),
  _bpConflictSelector(CS_MOST_RECENT),
  _bpConservativeAssignmentSelection(true),
  _bpFmElimination(true),
  _bpPropagateAfterConflict(true),
  _bpStartWithPrecise(false),
  _bpStartWithRational(false),
  _bpVariableSelector(VS_TIGHTEST_BOUND),

  _colorUnblocking(false),
  _condensation(CONDENSATION_OFF),

  _demodulationRedundancyCheck(true),
  _distinctProcessor(false),

  _eprPreservingNaming(false),
  _eprPreservingSkolemization(false),
  _eprRestoringInlining(false),
  _equalityPropagation(false),
  _equalityProxy(EP_OFF), 
  _equalityResolutionWithDeletion(RA_INPUT_ONLY),
  _equivalentVariableRemoval(true),
  _extensionalityResolution(ER_OFF),
  _extensionalityMaxLength(0),
  _extensionalityAllowPosEq(false),
  
  _flattenTopLevelConjunctions(false),
  _forceIncompleteness(false),
  _forwardDemodulation(DEMODULATION_ALL),
  _forwardLiteralRewriting(false),
  _forwardSubsumption(true),
  _forwardSubsumptionResolution(true),
  _functionDefinitionElimination(FDE_ALL),
  _functionNumber(1),

  _generalSplitting(RA_OFF),
  _globalSubsumption(false),

  _hornRevealing(false),
  _hyperSuperposition(false),

  _ignoreMissing(false),
  _include(""),
  _increasedNumeralWeight(false),
  _inequalitySplitting(3),
  _inputFile(""),
  //in case we compile vampire with bpa, then the default input syntax is smtlib
#if !GNUMP
  _inputSyntax(IS_TPTP),
#else
  _inputSyntax(IS_SMTLIB),
#endif
  _instGenBigRestartRatio(0.0f),
  _instGenInprocessing(false),
  _instGenPassiveReactivation(false),
  _instGenResolutionRatioInstGen(1),
  _instGenResolutionRatioResolution(1),
  _instGenRestartPeriod(1000),
  _instGenRestartPeriodQuotient(1.0f),
  _instGenSelection(0),
  _instGenWithResolution(false),
  _interpretedSimplification(false),

  _latexOutput("off"),
  _lingvaAdditionalInvariants(""),
  _literalComparisonMode(LCM_STANDARD),
  _logFile("off"),
  _lrsFirstTimeCheck(5),
  _lrsWeightLimitOnly(false),

  _maxActive(0),
  _maxAnswers(1),
  _maxInferenceDepth(0),
  _maxPassive(0),
  _maxWeight(0),
  _maximalPropagatedEqualityLength(5),
#if VDEBUG
  _memoryLimit(1000),
#else
  _memoryLimit(3000),
#endif
  _mode(MODE_VAMPIRE),

  _multiProofAttemptPriority(-1), // if -1 then we should overwrite with place in file
  _multiProofAttemptConcurrent(0), // if 0 we should take the number of strategies

  _namePrefix(""),
  _naming(8),

  _nicenessOption(NICENESS_AVERAGE),

  _nongoalWeightCoefficient(1.0),
  _nonGoalWeightCoeffitientDenominator(1),
  _nonGoalWeightCoeffitientNumerator(1),
  _nonliteralsInClauseWeight(false),
  _normalize(false),

  _outputAxiomNames(false),

  _predicateDefinitionInlining(INL_OFF),
  _predicateDefinitionMerging(false),
  _predicateEquivalenceDiscovery(PED_OFF),
  _predicateEquivalenceDiscoveryAddImplications(false),
  _predicateEquivalenceDiscoveryRandomSimulation(true),
  _predicateEquivalenceDiscoverySatConflictLimit(-1),
  _predicateIndexIntroduction(false),
  _printClausifierPremises(false),
  _problemName("unknown"),
  _proof(PROOF_ON),
  _proofChecking(false),
  _protectedPrefix(""),

  _questionAnswering(QA_OFF),

  _randomSeed(Random::seed()),
  _rowVariableMaxLength(2),

  _satClauseActivityDecay(1.001f),
  _satClauseDisposer(SCD_MINISAT),
  _satLearntMinimization(true),
  _satLearntSubsumptionResolution(true),
  _satLingelingIncremental(false),
  _satLingelingSimilarModels(false),
  _satRestartFixedCount(16000),
  _satRestartGeometricIncrease(1.1f),
  _satRestartGeometricInit(32),
  _satRestartLubyFactor(100),
  _satRestartMinisatIncrease(1.1f),
  _satRestartMinisatInit(100),
  _satRestartStrategy(SRS_LUBY),
  _satVarActivityDecay(1.05f),
  _satVarSelector(SVS_ACTIVE),
  _satSolver(MINISAT),
  _saturationAlgorithm(LRS),
  _selection(10),
  _selectUnusedVariablesFirst(false),
  _showActive(false),
  _showBlocked(false),
  _showDefinitions(false),
  _showInterpolant(INTERP_OFF),
  _showNew(false),
  _showNewPropositional(false),
  _showNonconstantSkolemFunctionTrace(false),
  _showOptions(false),
  _showPassive(false),
  _showPreprocessing(false),
  _showSkolemisations(false),
  _showSymbolElimination(false),
  _showTheoryAxioms(false),
  _simulatedTimeLimit(0),
  _sineDepth(0),
  _sineGeneralityThreshold(0),
  _sineSelection(SS_OFF),
  _sineTolerance(1.0f),
  _smtlibConsiderIntsReal(false),
  _smtlibFletAsDefinition(false),
  _smtlibIntroduceAIGNames(true),
  _sos(SOS_OFF),
  _splitAtActivation(false), // is this even a valid option?
  _splitting(true), // should splitting by on or off by default?
  _ssplittingAddComplementary(SSAC_GROUND),
  _ssplittingComponentSweeping(SSCS_ITERATED),
  _ssplittingCongruenceClosure(false),
  //_ssplittingEagerRemoval(true),//Removing the static field
  _ssplittingFlushPeriod(0),
  _ssplittingFlushQuotient(1.5f),
  _ssplittingNonsplittableComponents(SSNS_KNOWN),
  _statistics(STATISTICS_FULL),
  _superpositionFromVariables(true),
  _symbolPrecedence(BY_ARITY),

  _tabulationBwRuleSubsumptionResolutionByLemmas(true),
  _tabulationFwRuleSubsumptionResolutionByLemmas(true),
  _tabulationGoalAgeRatio(1),
  _tabulationGoalWeightRatio(1),
  _tabulationGoalRatio(1),
  _tabulationLemmaRatio(1),
  _tabulationInstantiateProducingRules(true),
  _tabulationLemmaAgeRatio(1),
  _tabulationLemmaWeightRatio(1),
  _testId ("unspecified_test"),
  _thanks("Tanya"),
  _theoryAxioms(true),
  _timeLimitInDeciseconds(600),
  _localTimeLimitInDeciseconds(600),
  _timeStatistics(false),
  _trivialPredicateRemoval(false),

  _unitResultingResolution(URR_OFF),
  _unusedPredicateDefinitionRemoval(true),
  _updatesByOneConstraint(3),
  _use_dm(false),

  _weightIncrement(false),
  _weightRatio(1),
  _whileNumber(1),

  _xmlOutput("off")
{
  CALL("Options::Options");
} // Options::Options

/**
 * Set option by its name and value.
 * @since 13/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing
 * @author Andrei Voronkov
 */
void Options::set(const char* name,const char* value)
{
  CALL ("Options::set/2");

  try {
    set(name,value,Constants::optionNames.find(name));
  }
  catch (const ValueNotFoundException&) {
    if (!_ignoreMissing) {
      USER_ERROR((vstring)name + " is not a valid option");
    }
  }
} // Options::set/2

/**
 * Set option by its name and value.
 * @since 06/04/2005 Torrevieja
 */
void Options::set(const vstring& name,const vstring& value)
{
  CALL ("Options::set/3");
  set(name.c_str(),value.c_str());
} // Options::set/3

/**
 * Set option by its name, value, and index in the list of options.
 * If index is -1, then name does not correspond to any existing option.
 *
 * @since 13/11/2004 Manchester
 */
void Options::set(const char* name,const char* value, int index)
{
  CALL("Options::set/3");

  int intValue;
  unsigned unsignedValue;
  float floatValue;

  try {
    switch (index) {
    case AGE_WEIGHT_RATIO:
      readAgeWeightRatio(value, _ageRatio, _weightRatio);
      return;
    case AIG_BDD_SWEEPING:
      _aigBddSweeping = onOffToBool(value,name);
      return;
    case AIG_CONDITIONAL_REWRITING:
      _aigConditionalRewriting = onOffToBool(value,name);
      return;
    case AIG_DEFINITION_INTRODUCTION:
      _aigDefinitionIntroduction = onOffToBool(value,name);
      return;
    case AIG_DEFINITION_INTRODUCTION_THRESHOLD:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	if (unsignedValue==0) {
	  USER_ERROR("aig_definition_introduction_threshold must be non-zero");
	}
	_aigDefinitionIntroductionThreshold = unsignedValue;
	return;
      }
      break;
    case AIG_FORMULA_SHARING:
      _aigFormulaSharing = onOffToBool(value,name);
      return;
    case AIG_INLINER:
      _aigInliner = onOffToBool(value,name);
      return;
    case ARITY_CHECK:
      _arityCheck = onOffToBool(value,name);
      return;

    case BACKWARD_DEMODULATION:
      _backwardDemodulation = (Demodulation)Constants::demodulationValues.find(value);
      return;
    case BACKWARD_SUBSUMPTION:
      _backwardSubsumption = (Subsumption)Constants::subsumptionValues.find(value);
      return;
    case BACKWARD_SUBSUMPTION_RESOLUTION:
      _backwardSubsumptionResolution = (Subsumption)Constants::subsumptionValues.find(value);
      return;
    case BFNT:
      _bfnt = onOffToBool(value,name);
      return;
    case BINARY_RESOLUTION:
      _binaryResolution = onOffToBool(value,name);
      return;
    case BP_ALLOWED_FM_BALANCE: {
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_bpAllowedFMBalance = unsignedValue;
      }
      else {
	USER_ERROR("The value must be an integer");
      }
      return;
    }
    case BP_ALMOST_HALF_BOUND_REMOVER:
      _bpAlmostHalfBoundingRemoval = (BPAlmostHalfBoundingRemoval)Constants::bpAlmostHalfBoundingRemovalValues.find(value);
      return;
    case BP_ASSIGNMENT_SELECTOR:
      _bpAssignmentSelector = (BPAssignmentSelector)Constants::bpAssignmentSelectorValues.find(value);
      return;
    case BP_COLLAPSING_PROPAGATION:
      _bpCollapsingPropagation = onOffToBool(value,name);
      return;
    case BP_CONFLICT_SELECTOR:
      _bpConflictSelector = (BPConflictSelector)Constants::bpConflictSelectorValues.find(value);
      return;
    case BP_CONSERVATIVE_ASSIGNMENT_SELECTION:
      _bpConservativeAssignmentSelection = onOffToBool(value,name);
      return;
    case BP_FM_ELIMINATION:
      _bpFmElimination = onOffToBool(value,name);
      return;
    case BP_MAX_PROP_LENGTH:
      if ( Int::stringToUnsignedInt(value, unsignedValue)) {
	_maximalPropagatedEqualityLength = unsignedValue;
      }
      else {
	USER_ERROR("the value must be an integer");
      }
      return;
    case BP_PROPAGATE_AFTER_CONFLICT:
      _bpPropagateAfterConflict = onOffToBool(value, name);
      return;
    case BP_START_WITH_PRECISE:
      _bpStartWithPrecise = onOffToBool(value,name);
      return;
    case BP_START_WITH_RATIONAL:
    	_bpStartWithRational = onOffToBool(value, name);
    	return;
    case BP_UPDATE_BY_ONE_CONSTRAINT:
      if ( Int::stringToUnsignedInt(value, unsignedValue)) {
	_updatesByOneConstraint = unsignedValue;
      }
      else USER_ERROR("The value must be an integer");
      return;
    case BP_VARIABLE_SELECTOR:
      _bpVariableSelector = (BPVariableSelector)Constants::bpVariableSelectorValues.find(value);
      return;

    case COLOR_UNBLOCKING:
      _colorUnblocking = onOffToBool(value,name);
      return;
    case CONDENSATION:
      _condensation =
	(Condensation)Constants::condensationValues.find(value);
      return;

    case DECODE:
      readFromTestId(value);
      return;
    case DEMODULATION_REDUNDANCY_CHECK:
      _demodulationRedundancyCheck = onOffToBool(value,name);
      return;
    case DISTINCT_PROCESSOR:
      _distinctProcessor = onOffToBool(value,name);
      return;

    case EPR_PRESERVING_NAMING:
      _eprPreservingNaming = onOffToBool(value,name);
      return;
    case EPR_PRESERVING_SKOLEMIZATION:
      _eprPreservingSkolemization = onOffToBool(value,name);
      return;
    case EPR_RESTORING_INLINING:
      _eprRestoringInlining = onOffToBool(value,name);
      return;
    case EQUALITY_PROPAGATION:
      _equalityPropagation = onOffToBool(value,name);
      return;
    case EQUALITY_PROXY:
      _equalityProxy = (EqualityProxy)Constants::equalityProxyValues.find(value);
      return;
    case EQUALITY_RESOLUTION_WITH_DELETION:
      _equalityResolutionWithDeletion = (RuleActivity)Constants::ruleActivityValues.find(value);
      if (_equalityResolutionWithDeletion==RA_ON) {
	USER_ERROR("equality_resolution_with_deletion is not implemented for value \"on\"");
      }
      return;
    case EXTENSIONALITY_RESOLUTION:
      _extensionalityResolution = (ExtensionalityResolution)Constants::extensionalityResolutionValues.find(value);
      return;
    case EXTENSIONALITY_MAX_LENGTH:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
        // 0 means infinity, so it is intentionally not if (unsignedValue < 2).
        if (unsignedValue == 1) {
          USER_ERROR("extensionality clauses have to be at least of size 2");
        }
	_extensionalityMaxLength = unsignedValue;
	return;
      }
      break;
    case EXTENSIONALITY_ALLOW_POS_EQ:
      _extensionalityAllowPosEq = onOffToBool(value,name);
      return;
      

    case FLATTEN_TOP_LEVEL_CONJUNCTIONS:
      _flattenTopLevelConjunctions = onOffToBool(value,name);
      return;
    case FORBIDDEN_OPTIONS:
      _forbiddenOptions = value;
      return;
    case FORCED_OPTIONS:
      _forcedOptions = value;
      return;
    case FORWARD_DEMODULATION:
      _forwardDemodulation =
	(Demodulation)Constants::demodulationValues.find(value);
      return;
    case FORWARD_LITERAL_REWRITING:
      _forwardLiteralRewriting = onOffToBool(value,name);
      return;
    case FORWARD_SUBSUMPTION:
      _forwardSubsumption = onOffToBool(value,name);
      return;
    case FORWARD_SUBSUMPTION_RESOLUTION:
      _forwardSubsumptionResolution = onOffToBool(value,name);
      return;
    case FUNCTION_DEFINITION_ELIMINATION:
      _functionDefinitionElimination =
	(FunctionDefinitionElimination)Constants::fdeValues.find(value);
      return;
    case FUNCTION_NUMBER:
      if (Int::stringToInt(value,intValue))
    	  _functionNumber= intValue;
      return;

    case GENERAL_SPLITTING:
      _generalSplitting = (RuleActivity)Constants::ruleActivityValues.find(value);
      if (_generalSplitting==RA_ON) {
	USER_ERROR("general_splitting is not implemented for value \"on\"");
      }
      return;
    case GLOBAL_SUBSUMPTION:
      _globalSubsumption = onOffToBool(value,name);
      return;

    case HORN_REVEALING:
      _hornRevealing = onOffToBool(value,name);
      return;
    case HYPER_SUPERPOSITION:
      _hyperSuperposition = onOffToBool(value,name);
      return;

    case IGNORE_MISSING:
      _ignoreMissing = onOffToBool(value,name);
      return;      
    case INCLUDE:
      _include = value;
      return;
    case INCREASED_NUMERAL_WEIGHT:
      _increasedNumeralWeight = onOffToBool(value,name);
      return;
    case INEQUALITY_SPLITTING:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_inequalitySplitting = unsignedValue;
	return;
      }
      break;
    case INPUT_FILE:
      setInputFile(value);
      return;
    case INPUT_SYNTAX:
      _inputSyntax = (InputSyntax)Constants::inputSyntaxValues.find(value);
      return;
    case INST_GEN_BIG_RESTART_RATIO:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<0.0f || floatValue>1.0f) {
	  USER_ERROR("inst_gen_big_restart_ratio must be a number between 0 and 1 (inclusive)");
	}
	_instGenBigRestartRatio = floatValue;
	return;
      }
      break;
    case INST_GEN_INPROCESSING:
      _instGenInprocessing = onOffToBool(value,name);
      return;
    case INST_GEN_PASSIVE_REACTIVATION:
      _instGenPassiveReactivation = onOffToBool(value,name);
      return;
    case INST_GEN_RESOLUTION_RATIO:
      readAgeWeightRatio(value, _instGenResolutionRatioInstGen, _instGenResolutionRatioResolution, '/');
      return;
    case INST_GEN_RESTART_PERIOD:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_instGenRestartPeriod = unsignedValue;
	return;
      }
      break;
    case INST_GEN_RESTART_PERIOD_QUOTIENT:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<1.0f) {
	  USER_ERROR("inst_gen_restart_period_quotient must be a number at least 1");
	}
	_instGenRestartPeriodQuotient = floatValue;
	return;
      }
      break;
    case INST_GEN_SELECTION:
      if (Int::stringToInt(value,intValue) &&
	  setInstGenSelection(intValue) ) {
	return;
      }
      break;
    case INST_GEN_WITH_RESOLUTION:
      _instGenWithResolution = onOffToBool(value,name);
      return;
    case INTERPRETED_SIMPLIFICATION:
      _interpretedSimplification = onOffToBool(value,name);
      return;

    case LATEX_OUTPUT:
      _latexOutput = value;
      return;

    case LINGVA_ADDITIONAL_INVARIANTS:
      _lingvaAdditionalInvariants = value;
      return;

    case LITERAL_COMPARISON_MODE:
      _literalComparisonMode =
	(LiteralComparisonMode)Constants::lcmValues.find(value);
      return;
    case LOG_FILE:
      _logFile = value;
      return;
    case LRS_FIRST_TIME_CHECK:
      if (Int::stringToInt(value,intValue) &&
	  setLrsFirstTimeCheck(intValue)) {
	return;
      }
      break;
    case LRS_WEIGHT_LIMIT_ONLY:
      _lrsWeightLimitOnly = onOffToBool(value,name);
      return;

    case MAX_ACTIVE:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_maxActive = unsignedValue;
	return;
      }
      break;
    case MAX_ANSWERS:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_maxAnswers = unsignedValue;
	return;
      }
      break;
    case MAX_INFERENCE_DEPTH:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_maxInferenceDepth = unsignedValue;
	return;
      }
      break;
    case MAX_PASSIVE:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_maxPassive = unsignedValue;
	return;
      }
      break;
    case MAX_WEIGHT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_maxWeight = unsignedValue;
	return;
      }
      break;
    case MEMORY_LIMIT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_memoryLimit = unsignedValue;
	return;
      }
      break;
    case MODE:
      _mode = (Mode)Constants::modeValues.find(value);
      return;

    case MULTI_PROOF_ATTEMPT_CONCURRENT:
      if(Int::stringToUnsignedInt(value,unsignedValue)){
         _multiProofAttemptConcurrent=unsignedValue;
         return;
      }
      break;

    case MULTI_PROOF_ATTEMPT_PRIORITY:
      if(Int::stringToInt(value,intValue)){
         _multiProofAttemptPriority=intValue;
         return;
      }
      break;

    case NAME_PREFIX:
      _namePrefix = value;
      return;
    case NAMING:
      if (Int::stringToUnsignedInt(value,unsignedValue) &&
	  setNaming(unsignedValue)) {
	return;
      }
      break;
    case NONGOAL_WEIGHT_COEFFICIENT:
      if (Int::stringToFloat(value,floatValue) &&
	  setNongoalWeightCoefficient(floatValue)) {
	return;
      }
      break;
    case NONLITERALS_IN_CLAUSE_WEIGHT:
      _nonliteralsInClauseWeight = onOffToBool(value,name);
      return;
    case NORMALIZE:
      _normalize = onOffToBool(value,name);
      return;

    case OUTPUT_AXIOM_NAMES:
      _outputAxiomNames = onOffToBool(value,name);
      return;

    case PREDICATE_DEFINITION_INLINING:
      _predicateDefinitionInlining = (InliningMode)Constants::inliningModeValues.find(value);
      return;
    case PREDICATE_DEFINITION_MERGING:
      _predicateDefinitionMerging = onOffToBool(value,name);
      return;
    case PREDICATE_EQUIVALENCE_DISCOVERY:
      _predicateEquivalenceDiscovery =
	  (PredicateEquivalenceDiscoveryMode)Constants::predicateEquivalenceDiscoveryModeValues.find(value);
      return;
    case PREDICATE_EQUIVALENCE_DISCOVERY_ADD_IMPLICATIONS:
      _predicateEquivalenceDiscoveryAddImplications = onOffToBool(value,name);
      return;
    case PREDICATE_EQUIVALENCE_DISCOVERY_RANDOM_SIMULATION:
      _predicateEquivalenceDiscoveryRandomSimulation = onOffToBool(value,name);
      return;
    case PREDICATE_EQUIVALENCE_DISCOVERY_SAT_CONFLICT_LIMIT:
      if (Int::stringToInt(value,intValue)) {
	_predicateEquivalenceDiscoverySatConflictLimit = intValue;
	return;
      }
      break;
    case PREDICATE_INDEX_INTRODUCTION:
      _predicateIndexIntroduction = onOffToBool(value,name);
      return;
    case PRINT_CLAUSIFIER_PREMISES:
      _printClausifierPremises = onOffToBool(value,name);
      return;
    case PROOF:
      _proof = (Proof)Constants::proofValues.find(value);
      return;
    case PROOF_CHECKING:
      _proofChecking = onOffToBool(value,name);
      return;
    case PROTECTED_PREFIX:
      _protectedPrefix = value;
      return;

    case QUESTION_ANSWERING:
      _questionAnswering = (QuestionAnsweringMode)Constants::questionAnsweringValues.find(value);
      return;

    case RANDOM_SEED:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_randomSeed = unsignedValue;
	return;
      }
      break;
    case ROW_VARIABLE_MAX_LENGTH:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_rowVariableMaxLength = unsignedValue;
	return;
      }
      break;

    case SAT_CLAUSE_ACTIVITY_DECAY:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<=1.0f) {
	  USER_ERROR("sat_clause_activity_decay must be a number greater than 1");
	}
	_satClauseActivityDecay = floatValue;
	return;
      }
      break;
    case SAT_CLAUSE_DISPOSER:
      _satClauseDisposer = (SatClauseDisposer)Constants::satClauseDisposerValues.find(value);
      return;
    case SAT_LEARNT_MINIMIZATION:
      _satLearntMinimization = onOffToBool(value,name);
      return;
    case SAT_LEARNT_SUBSUMPTION_RESOLUTION:
      _satLearntSubsumptionResolution = onOffToBool(value,name);
      return;

    case SAT_LINGELING_INCREMENTAL:
      _satLingelingIncremental = onOffToBool(value, name);
      return;
    case SAT_LINGELING_SIMILAR_MODELS:
      _satLingelingSimilarModels = onOffToBool(value, name);
      return;

    case SAT_RESTART_FIXED_COUNT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_satRestartFixedCount = unsignedValue;
	return;
      }
      break;
    case SAT_RESTART_GEOMETRIC_INCREASE:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<=1.0f) {
	  USER_ERROR("sat_restart_geometric_increase must be a number greater than 1");
	}
	_satRestartGeometricIncrease = floatValue;
	return;
      }
      break;
    case SAT_RESTART_GEOMETRIC_INIT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_satRestartGeometricInit = unsignedValue;
	return;
      }
      break;
    case SAT_RESTART_LUBY_FACTOR:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_satRestartLubyFactor = unsignedValue;
	return;
      }
      break;
    case SAT_RESTART_MINISAT_INCREASE:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<=1.0f) {
	  USER_ERROR("sat_restart_minisat_increase must be a number greater than 1");
	}
	_satRestartMinisatIncrease = floatValue;
	return;
      }
      break;
    case SAT_RESTART_MINISAT_INIT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_satRestartMinisatInit = unsignedValue;
	return;
      }
      break;
    case SAT_RESTART_STRATEGY:
      _satRestartStrategy = (SatRestartStrategy)Constants::satRestartStrategyValues.find(value);
      return;
    case SAT_VAR_ACTIVITY_DECAY:
      if (Int::stringToFloat(value,floatValue)) {
	if (floatValue<=1.0f) {
	  USER_ERROR("sat_var_activity_decay must be a number greater than 1");
	}
	_satVarActivityDecay = floatValue;
	return;
      }
      break;
    case SAT_VAR_SELECTOR:
      _satVarSelector = (SatVarSelector)Constants::satVarSelectorValues.find(value);
      return;
    case NICENESS_OPTION:
      _nicenessOption = (NicenessOption)Constants::nicenessOptionValues.find(value);
      return;
    case SAT_SOLVER:
      _satSolver = (SatSolver) Constants::satSolverValues.find(value);
      return;
    case SATURATION_ALGORITHM:
      _saturationAlgorithm = (SaturationAlgorithm)Constants::satAlgValues.find(value);
      return;
    case SELECTION:
      if (Int::stringToInt(value,intValue) &&
	  setSelection(intValue) ) {
	return;
      }
      break;
    case SHOW_ACTIVE:
      _showActive = onOffToBool(value,name);
      return;
    case SHOW_BLOCKED:
      _showBlocked = onOffToBool(value,name);
      return;
    case SHOW_DEFINITIONS:
      _showDefinitions = onOffToBool(value,name);
      return;
    case SHOW_INTERPOLANT:
      _showInterpolant = (InterpolantMode)Constants::interpolantModeValues.find(value);
      return;
    case SHOW_NEW:
      _showNew = onOffToBool(value,name);
      return;
    case SHOW_NEW_PROPOSITIONAL:
      _showNewPropositional = onOffToBool(value,name);
      return;
    case SHOW_NONCONSTANT_SKOLEM_FUNCTION_TRACE:
      _showNonconstantSkolemFunctionTrace = onOffToBool(value,name);
      return;
    case SHOW_OPTIONS:
      _showOptions = onOffToBool(value,name);
      return;
    case SHOW_PASSIVE:
      _showPassive = onOffToBool(value,name);
      return;
    case SHOW_PREPROCESSING:
      _showPreprocessing = onOffToBool(value,name);
      return;
    case SHOW_SKOLEMISATIONS:
      _showSkolemisations = onOffToBool(value,name);
      return;
    case SHOW_SYMBOL_ELIMINATION:
      _showSymbolElimination = onOffToBool(value,name);
      return;
    case SHOW_THEORY_AXIOMS:
      _showTheoryAxioms = onOffToBool(value,name);
      return;
    case SIMULATED_TIME_LIMIT:
      _simulatedTimeLimit = readTimeLimit(value);
      return;
    case SINE_DEPTH:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_sineDepth = unsignedValue;
	return;
      }
      break;
    case SINE_GENERALITY_THRESHOLD:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_sineGeneralityThreshold = unsignedValue;
	return;
      }
      break;
    case SINE_SELECTION:
      _sineSelection =
	(SineSelection)Constants::sineSelectionValues.find(value);
      return;
    case SINE_TOLERANCE:
      if (!Int::stringToFloat(value,floatValue) || (floatValue!=0.0f && floatValue<1.0f)) {
	USER_ERROR("sine_tolerance value must be a float number greater than or equal to 1");
      }
      _sineTolerance = floatValue;
      return;
    case SMTLIB_CONSIDER_INTS_REAL:
      _smtlibConsiderIntsReal = onOffToBool(value,name);
      return;
    case SMTLIB_FLET_AS_DEFINITION:
      _smtlibFletAsDefinition = onOffToBool(value,name);
      return;
    case SMTLIB_INTRODUCE_AIG_NAMES:
      _smtlibIntroduceAIGNames = onOffToBool(value,name);
      return;
    case SOS:
      _sos = (Sos)Constants::sosValues.find(value);
      return;
    case SPLIT_AT_ACTIVATION:
      _splitAtActivation = onOffToBool(value,name);
      return;
    case SPLITTING:
      _splitting = onOffToBool(value,name);//(SplittingMode)Constants::splittingModeValues.find(value);
      return;
    case SSPLITTING_ADD_COMPLEMENTARY:
      _ssplittingAddComplementary = (SSplittingAddComplementary)Constants::sSplittingAddComplementaryValues.find(value);
      return;
    case SSPLITTING_COMPONENT_SWEEPING:
      _ssplittingComponentSweeping = (SSplittingComponentSweeping)Constants::sSplittingComponentSweepingValues.find(value);
      return;
    case SSPLITTING_CONGRUENCE_CLOSURE:
      _ssplittingCongruenceClosure = onOffToBool(value,name);
      return;
    case SSPLITTING_EAGER_REMOVAL:
      _ssplittingEagerRemoval = onOffToBool(value,name);
      return;
    case SSPLITTING_FLUSH_PERIOD:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_ssplittingFlushPeriod = unsignedValue;
	return;
      }
      break;
    case SSPLITTING_FLUSH_QUOTIENT:
      if (!Int::stringToFloat(value,floatValue) || (floatValue<1.0f)) {
	USER_ERROR("ssplitting_flush_quotient must greater than or equal to 1");
      }
      _ssplittingFlushQuotient = floatValue;
      return;
    case SSPLITTING_NONSPLITTABLE_COMPONENTS:
      _ssplittingNonsplittableComponents = (SSplittingNonsplittableComponents)Constants::sSplittingNonsplittableComponentsValues.find(value);
      return;
      
    case STATISTICS:
      _statistics = (Statistics)Constants::statisticsValues.find(value);
      return;
    case SUPERPOSITION_FROM_VARIABLES:
      _superpositionFromVariables = onOffToBool(value,name);
      return;
    case SYMBOL_PRECEDENCE:
      _symbolPrecedence =
	(SymbolPrecedence)Constants::symbolPrecedenceValues.find(value);
      return;

    case TABULATION_BW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS:
      _tabulationBwRuleSubsumptionResolutionByLemmas = onOffToBool(value,name);
      return;
    case TABULATION_FW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS:
      _tabulationFwRuleSubsumptionResolutionByLemmas = onOffToBool(value,name);
      return;
    case TABULATION_GOAL_AWR:
      readAgeWeightRatio(value, _tabulationGoalAgeRatio, _tabulationGoalWeightRatio, '/');
      return;
    case TABULATION_GOAL_LEMMA_RATIO:
      readAgeWeightRatio(value, _tabulationGoalRatio, _tabulationLemmaRatio, '/');
      return;
    case TABULATION_INSTANTIATE_PRODUCING_RULES:
      _tabulationInstantiateProducingRules = onOffToBool(value,name);
      return;
    case TABULATION_LEMMA_AWR:
      readAgeWeightRatio(value, _tabulationLemmaAgeRatio, _tabulationLemmaWeightRatio, '/');
      return;
    case TEST_ID:
      _testId = value;
      return;
    case THANKS:
      _thanks = value;
      return;
    case THEORY_AXIOMS:
      _theoryAxioms = onOffToBool(value,name);
      return;
    case TIME_LIMIT:
      _timeLimitInDeciseconds = readTimeLimit(value);
      return;
    case TIME_LIMIT_LOCAL:
      _localTimeLimitInDeciseconds = readTimeLimit(value);
      return;
    case TIME_STATISTICS:
      _timeStatistics = onOffToBool(value,name);
      return;
    case TRIVIAL_PREDICATE_REMOVAL:
      _trivialPredicateRemoval = onOffToBool(value,name);
      return;

    case UNIT_RESULTING_RESOLUTION:
      _unitResultingResolution = (URResolution)Constants::urResolutionValues.find(value);
      return;
    case UNUSED_PREDICATE_DEFINITION_REMOVAL:
      _unusedPredicateDefinitionRemoval = onOffToBool(value,name);
      return;

    case USEDM:
      _use_dm = onOffToBool(value,name);
      return;

    case WEIGHT_INCREMENT:
      _weightIncrement = onOffToBool(value,name);
      return;
    case WHILE_NUMBER:
       if (Int::stringToInt(value,intValue))
       _whileNumber = intValue;
       return;

    case XML_OUTPUT:
      _xmlOutput = value;
      return;


#if VDEBUG
    default:
      ASSERTION_VIOLATION_REP(name);
#endif
    }
    throw ValueNotFoundException();
  }
  catch(ValueNotFoundException&) {
    USER_ERROR((vstring)"wrong value (" + value + ") for " + name);
  }
} // Options::set


/**
 * Set option by its short name and value. If such a short name does not
 * exist, try to use the long name instead.
 *
 * @since 21/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing
 * @author Andrei Voronkov
 */
void Options::setShort(const char* name,const char* value)
{
  CALL ("Options::setShort");

  int found;
  try {
    found = Constants::shortNameIndexes[Constants::shortNames.find(name)];
  }
  catch(ValueNotFoundException&) {
    // try to set it as a long name
    return set(name,value);
  }
  set(name,value,found);
} // Options::setShort

/**
 * Convert the string onOff to a boolean value. If onOff is not one
 * of "on" or "off", then raise a user error exception.
 * @since 15/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing for the splitting option
 * @author Andrei Voronkov
 */
bool Options::onOffToBool (const char* onOff,const char* option)
{
  CALL("Options::onOffToBool");

  if (! strcmp(onOff,"on")) {
    return true;
  }
  if (! strcmp(onOff,"off")) {
    return false;
  }
  if (_ignoreMissing) {
    if (!strcmp(option,"splitting") || !strcmp(option,"spl")) {
      if (! strcmp(onOff,"sat")) {
	return true;
      }
    }
  }
  
  USER_ERROR((vstring)"wrong value for " + option + ": " + onOff);
} // Options::onOffToBool

/**
 * Convert a boolean value to the corresponding string "on"/"off"
 * value.
 * @since 15/11/2004 Manchester
 */
vstring Options::boolToOnOff (bool val)
{
  CALL("Options::boolToOnOff");

  static vstring on ("on");
  static vstring off ("off");

  return val ? on : off;
} // Options::boolToOnOff


/**
 * Set selection to a new value.
 * @since 15/11/2004 Manchester
 */
bool Options::setSelection(int sel)
{
  CALL("Options::setSelection");

  switch (sel) {
  case 0:
  case 1:
  case 2:
  case 3:
  case 4:
  case 10:
  case 11:
  case 1002:
  case 1003:
  case 1004:
  case 1010:
  case 1011:
  case -1:
  case -2:
  case -3:
  case -4:
  case -10:
  case -11:
  case -1002:
  case -1003:
  case -1004:
  case -1010:
    _selection = sel;
    return true;
  default:
    return false;
  }
} // Options::setSelection

/**
 * Set instGenSelection to a new value.
 */
bool Options::setInstGenSelection(int sel)
{
  CALL("Options::setInstGenSelection");

  switch (sel) {
  case 0:
  case 1:
  case 2:
  case 3:
  case 4:
  case 10:
  case 1002:
  case 1003:
  case 1004:
  case 1010:
  case -1:
  case -2:
  case -3:
  case -4:
  case -10:
  case -1002:
  case -1003:
  case -1004:
  case -1010:
    _instGenSelection = sel;
    return true;
  default:
    return false;
  }
} // Options::setSelection


/**
 * Set nongoal weight coefficient to a new value.
 * @since 15/11/2004 Manchester.
 */
bool Options::setNongoalWeightCoefficient (float newVal)
{
  CALL("Options::setNongoalWeightCoefficient");

  if (newVal <= 0.0) {
    return false;
  }
  _nongoalWeightCoefficient = newVal;

  //convert the coeffitient to rationsl (we don't need to be super precise so we do it as below...)
  _nonGoalWeightCoeffitientNumerator = static_cast<int>(_nongoalWeightCoefficient*100);
  _nonGoalWeightCoeffitientDenominator = 100;

  return true;
} // Options::setNongoalWeightCoefficient


/**
 * Set naming to a new value.
 * @since 13/07/2005 Haifa
 */
bool Options::setNaming (int newVal)
{
  CALL("Options::setNaming");

  if (newVal > 32767) {
    return false;
  }
  _naming = newVal;
  return true;
} // Options::setNaming


/**
 * Set LRS first time check.
 * @since 15/11/2004 Manchester.
 */
bool Options::setLrsFirstTimeCheck (int newVal)
{
  CALL("Options::setLrsFirstTimeCheck");

  if (newVal < 0 && newVal >= 100) {
    return false;
  }
  _lrsFirstTimeCheck = newVal;
  return true;
} // Options::setLrsFirstTimeCheck


/**
 * Return the include file name using its relative name.
 *
 * @param relativeName the relative name, must begin and end with "'"
 *        because of the TPTP syntax
 * @since 16/10/2003 Manchester, relativeName changed to string from char*
 * @since 07/08/2014 Manchester, relativeName changed to vstring
 */
vstring Options::includeFileName (const vstring& relativeName)
{
  CALL("Options::includeFileName");

  if (relativeName[0] == '/') { // absolute name
    return relativeName;
  }

  if (System::fileExists(relativeName)) {
    return relativeName;
  }

  // truncatedRelativeName is relative.
  // Use the conventions of Vampire:
  // (a) first search the value of "include"
  vstring dir = include();

  if (dir == "") { // include undefined
    // (b) search in the directory of the 'current file'
    // i.e. the input file
    vstring currentFile = inputFile();
    System::extractDirNameFromPath(currentFile,dir); 
    if(System::fileExists(dir+"/"+relativeName)){
      return dir + "/" + relativeName;
    }

    // (c) search the value of the environment variable TPTP_DIR
    char* env = getenv("TPTP");
    if (env) {
      dir = env;
    }
    else {
    // (d) use the current directory
      dir = ".";
    }
    // we do not check (c) or (d) - an error will occur later
    // if the file does not exist here
  }
  // now dir is the directory to search
  return dir + "/" + relativeName;
} // Options::includeFileName


/**
 * Output options to a stream.
 *
 * @param str the stream
 * @since 02/01/2003 Manchester
 * @since 28/06/2003 Manchester, changed to treat XML output as well
 * @since 10/07/2003 Manchester, "normalize" added.
 * @since 27/11/2003 Manchester, changed using new XML routines and iterator
 *        of options
 */
void Options::output (ostream& str) const
{
  CALL("Options::output");

  if (! showOptions()) {
    return;
  }

  str << "=========== Options ==========\n";

  for (int i = 0;i < Constants::optionNames.length;i++) {
    str << Constants::optionNames[i] << '=';
    outputValue(str,i);
    str << '\n';
  }

  str << "======= End of options =======\n";
} // Options::output (ostream& str) const

/**
 * Output the value of an option with a given tag to the output stream
 * str.
 *
 * @since 15/11/2004 Manchester
 */
void Options::outputValue (ostream& str,int optionTag) const
{
  CALL("Options::outputValue");

  switch (optionTag) {
  case AGE_WEIGHT_RATIO:
    str << _ageRatio << ':' << _weightRatio;
    return;
  case AIG_BDD_SWEEPING:
    str << boolToOnOff(_aigBddSweeping);
    return;
  case AIG_CONDITIONAL_REWRITING:
    str << boolToOnOff(_aigConditionalRewriting);
    return;
  case AIG_DEFINITION_INTRODUCTION:
    str << boolToOnOff(_aigDefinitionIntroduction);
    return;
  case AIG_DEFINITION_INTRODUCTION_THRESHOLD:
    str << _aigDefinitionIntroductionThreshold;
    return;
  case AIG_FORMULA_SHARING:
    str << boolToOnOff(_aigFormulaSharing);
    return;
  case AIG_INLINER:
    str << boolToOnOff(_aigInliner);
    return;
  case ARITY_CHECK:
    str << boolToOnOff(_arityCheck);
    return;
  case BACKWARD_DEMODULATION:
    str << Constants::demodulationValues[_backwardDemodulation];
    return;
  case BACKWARD_SUBSUMPTION:
    str << Constants::subsumptionValues[_backwardSubsumption];
    return;
  case BACKWARD_SUBSUMPTION_RESOLUTION:
    str << Constants::subsumptionValues[_backwardSubsumptionResolution];
    return;
  case BFNT:
    str << boolToOnOff(_bfnt);
    return;
  case BINARY_RESOLUTION:
    str << boolToOnOff(_binaryResolution);
    return;
  case BP_ALLOWED_FM_BALANCE:
    str << _bpAllowedFMBalance;
    return;
  case BP_ALMOST_HALF_BOUND_REMOVER:
    str << Constants::bpAlmostHalfBoundingRemovalValues[_bpAlmostHalfBoundingRemoval];
    return;
  case BP_ASSIGNMENT_SELECTOR:
    str << Constants::bpAssignmentSelectorValues[_bpAssignmentSelector];
    return;
  case BP_CONFLICT_SELECTOR:
    str << Constants::bpConflictSelectorValues[_bpConflictSelector];
    return;
  case BP_CONSERVATIVE_ASSIGNMENT_SELECTION:
    str << boolToOnOff(_bpConservativeAssignmentSelection);
    return;
  case BP_COLLAPSING_PROPAGATION:
    str << boolToOnOff(_bpCollapsingPropagation);
    return;
  case BP_FM_ELIMINATION:
    str << boolToOnOff(_bpFmElimination);
    return;
  case BP_MAX_PROP_LENGTH:
    str << _maximalPropagatedEqualityLength;
    return;
  case BP_PROPAGATE_AFTER_CONFLICT:
	str << boolToOnOff(_bpPropagateAfterConflict);
	return;
  case BP_START_WITH_PRECISE:
    str << boolToOnOff(_bpStartWithPrecise);
    return;
  case BP_START_WITH_RATIONAL:
	  str<< boolToOnOff(_bpStartWithRational);
	  return;
  case BP_UPDATE_BY_ONE_CONSTRAINT:
    str << _updatesByOneConstraint;
    return;
  case BP_VARIABLE_SELECTOR:
    str << Constants::bpVariableSelectorValues[_bpVariableSelector];
    return;

  case COLOR_UNBLOCKING:
    str << boolToOnOff(_colorUnblocking);
    return;
  case CONDENSATION:
    str << Constants::condensationValues[_condensation];
    return;
  case DECODE: // no output for DECODE
    return;
  case DEMODULATION_REDUNDANCY_CHECK:
    str << boolToOnOff(_demodulationRedundancyCheck);
    return;
  case DISTINCT_PROCESSOR:
    str << boolToOnOff(_distinctProcessor);
    return;

  case EPR_PRESERVING_NAMING:
    str << boolToOnOff(_eprPreservingNaming);
    return;
  case EPR_PRESERVING_SKOLEMIZATION:
    str << boolToOnOff(_eprPreservingSkolemization);
    return;
  case EPR_RESTORING_INLINING:
    str << boolToOnOff(_eprRestoringInlining);
    return;
  case EQUALITY_PROPAGATION:
    str << boolToOnOff(_equalityPropagation);
    return;
  case EQUALITY_PROXY:
    str << Constants::equalityProxyValues[_equalityProxy];
    return;
  case EQUALITY_RESOLUTION_WITH_DELETION:
    str << Constants::ruleActivityValues[_equalityResolutionWithDeletion];
    return;
  case EXTENSIONALITY_RESOLUTION:
    str << Constants::extensionalityResolutionValues[_extensionalityResolution];
    return;

  case FLATTEN_TOP_LEVEL_CONJUNCTIONS:
    str << boolToOnOff(_flattenTopLevelConjunctions);
    return;
  case FORBIDDEN_OPTIONS:
    str << forbiddenOptions();
    return;
  case FORCED_OPTIONS:
    str << forcedOptions();
    return;
  case FORWARD_DEMODULATION:
    str << Constants::demodulationValues[_forwardDemodulation];
    return;
  case FORWARD_LITERAL_REWRITING:
    str << boolToOnOff(_forwardLiteralRewriting);
    return;
  case FORWARD_SUBSUMPTION:
    str << boolToOnOff(_forwardSubsumption);
    return;
  case FORWARD_SUBSUMPTION_RESOLUTION:
    str << boolToOnOff(_forwardSubsumptionResolution);
    return;
  case FUNCTION_DEFINITION_ELIMINATION:
    str << Constants::fdeValues[_functionDefinitionElimination];
    return;

  case GENERAL_SPLITTING:
    str << Constants::ruleActivityValues[_generalSplitting];
    return;
  case GLOBAL_SUBSUMPTION:
    str << boolToOnOff(_globalSubsumption);
    return;

  case HORN_REVEALING:
    str << boolToOnOff(_hornRevealing);
    return;
  case HYPER_SUPERPOSITION:
    str << boolToOnOff(_hyperSuperposition);
    return;

  case IGNORE_MISSING:
    str << boolToOnOff(_ignoreMissing);
    return;
  case INCLUDE:
    str << _include;
    return;
  case INCREASED_NUMERAL_WEIGHT:
    str << boolToOnOff(_increasedNumeralWeight);
    return;
  case INEQUALITY_SPLITTING:
    str << _inequalitySplitting;
    return;
  case INPUT_FILE:
    str << _inputFile;
    return;
  case INPUT_SYNTAX:
    str << Constants::inputSyntaxValues[_inputSyntax];
    return;
  case INST_GEN_BIG_RESTART_RATIO:
    str << _instGenBigRestartRatio;
    return;
  case INST_GEN_INPROCESSING:
    str << boolToOnOff(_instGenInprocessing);
    return;
  case INST_GEN_PASSIVE_REACTIVATION:
    str << boolToOnOff(_instGenPassiveReactivation);
    return;
  case INST_GEN_RESOLUTION_RATIO:
    str << _instGenResolutionRatioInstGen << ':' << _instGenResolutionRatioResolution;
    return;
  case INST_GEN_RESTART_PERIOD:
    str << _instGenRestartPeriod;
    return;
  case INST_GEN_RESTART_PERIOD_QUOTIENT:
    str << _instGenRestartPeriodQuotient;
    return;
  case INST_GEN_SELECTION:
    str << _instGenSelection;
    return;
  case INST_GEN_WITH_RESOLUTION:
    str << boolToOnOff(_instGenWithResolution);
    return;
  case INTERPRETED_SIMPLIFICATION:
    str << boolToOnOff(_interpretedSimplification);
    return;

  case LATEX_OUTPUT:
    str << _latexOutput;
    return;
  case LINGVA_ADDITIONAL_INVARIANTS:
    str << _lingvaAdditionalInvariants;
    return;
  case LITERAL_COMPARISON_MODE:
    str << Constants::lcmValues[_literalComparisonMode];
    return;
  case LOG_FILE:
    str << _logFile;
    return;
  case LRS_FIRST_TIME_CHECK:
    str << _lrsFirstTimeCheck;
    return;
  case LRS_WEIGHT_LIMIT_ONLY:
    str << boolToOnOff(_lrsWeightLimitOnly);
    return;

  case MAX_ACTIVE:
    str << _maxActive;
    return;
  case MAX_ANSWERS:
    str << _maxAnswers;
    return;
  case MAX_INFERENCE_DEPTH:
    str << _maxInferenceDepth;
    return;
  case MAX_PASSIVE:
    str << _maxPassive;
    return;
  case MAX_WEIGHT:
    str << _maxWeight;
    return;
  case MEMORY_LIMIT:
    str << _memoryLimit;
    return;
  case MODE:
    str << Constants::modeValues[_mode];
    return;

  case NAME_PREFIX:
    str << _namePrefix;
    return;
  case NAMING:
    str << _naming;
    return;
  case NONGOAL_WEIGHT_COEFFICIENT:
    str << _nongoalWeightCoefficient;
    return;
  case NONLITERALS_IN_CLAUSE_WEIGHT:
    str << boolToOnOff(_nonliteralsInClauseWeight);
    return;
  case NORMALIZE:
    str << boolToOnOff(_normalize);
    return;

  case OUTPUT_AXIOM_NAMES:
    str << boolToOnOff(_outputAxiomNames);
    return;

  case PREDICATE_DEFINITION_INLINING:
    str << Constants::inliningModeValues[_predicateDefinitionInlining];
    return;
  case PREDICATE_DEFINITION_MERGING:
    str << boolToOnOff(_predicateDefinitionMerging);
    return;
  case PREDICATE_EQUIVALENCE_DISCOVERY:
    str << Constants::predicateEquivalenceDiscoveryModeValues[_predicateEquivalenceDiscovery];
    return;
  case PREDICATE_EQUIVALENCE_DISCOVERY_ADD_IMPLICATIONS:
    str << boolToOnOff(_predicateEquivalenceDiscoveryAddImplications);
    return;
  case PREDICATE_EQUIVALENCE_DISCOVERY_RANDOM_SIMULATION:
    str << boolToOnOff(_predicateEquivalenceDiscoveryRandomSimulation);
    return;
  case PREDICATE_EQUIVALENCE_DISCOVERY_SAT_CONFLICT_LIMIT:
    str << _predicateEquivalenceDiscoverySatConflictLimit;
    return;
  case PREDICATE_INDEX_INTRODUCTION:
    str << boolToOnOff(_predicateIndexIntroduction);
    return;
  case PRINT_CLAUSIFIER_PREMISES:
    str << boolToOnOff(_printClausifierPremises);
    return;
  case PROBLEM_NAME:
    str << _problemName;
    return;
  case PROOF:
    str << boolToOnOff(_proof);
    return;
  case PROOF_CHECKING:
    str << boolToOnOff(_proofChecking);
    return;
  case PROTECTED_PREFIX:
    str << _protectedPrefix;
    return;

  case QUESTION_ANSWERING:
    str << Constants::questionAnsweringValues[_questionAnswering];
    return;

  case RANDOM_SEED:
    str << _randomSeed;
    return;
  case ROW_VARIABLE_MAX_LENGTH:
    str << _rowVariableMaxLength;
    return;

  case SAT_CLAUSE_ACTIVITY_DECAY:
    str << _satClauseActivityDecay;
    return;
  case SAT_CLAUSE_DISPOSER:
    str << Constants::satClauseDisposerValues[_satClauseDisposer];
    return;
  case SAT_LEARNT_MINIMIZATION:
    str << boolToOnOff(_satLearntMinimization);
    return;
  case SAT_LEARNT_SUBSUMPTION_RESOLUTION:
    str << boolToOnOff(_satLearntSubsumptionResolution);
    return;
  case SAT_LINGELING_INCREMENTAL:
	str << boolToOnOff(_satLingelingIncremental);
	return;
  case SAT_LINGELING_SIMILAR_MODELS:
	str << boolToOnOff(_satLingelingSimilarModels);
	return;
  case SAT_RESTART_FIXED_COUNT:
    str << _satRestartFixedCount;
    return;
  case SAT_RESTART_GEOMETRIC_INCREASE:
    str << _satRestartGeometricIncrease;
    return;
  case SAT_RESTART_GEOMETRIC_INIT:
    str << _satRestartGeometricInit;
    return;
  case SAT_RESTART_LUBY_FACTOR:
    str << _satRestartLubyFactor;
    return;
  case SAT_RESTART_MINISAT_INCREASE:
    str << _satRestartMinisatIncrease;
    return;
  case SAT_RESTART_MINISAT_INIT:
    str << _satRestartMinisatInit;
    return;
  case SAT_RESTART_STRATEGY:
    str << Constants::satRestartStrategyValues[_satRestartStrategy];
    return;
  case SAT_VAR_ACTIVITY_DECAY:
    str << _satVarActivityDecay;
    return;
  case SAT_VAR_SELECTOR:
    str << Constants::satVarSelectorValues[_satVarSelector];
    return;
  case NICENESS_OPTION:
    str << Constants::nicenessOptionValues[_nicenessOption];
  case SAT_SOLVER:
    str << Constants::satSolverValues[_satSolver];
    return;
  case SATURATION_ALGORITHM:
    str << Constants::satAlgValues[_saturationAlgorithm];
    return;
  case SELECTION:
    str << _selection;
    return;
  case SHOW_ACTIVE:
    str << boolToOnOff(_showActive);
    return;
  case SHOW_BLOCKED:
    str << boolToOnOff(_showBlocked);
    return;
  case SHOW_DEFINITIONS:
    str << boolToOnOff(_showDefinitions);
    return;
  case SHOW_INTERPOLANT:
    str << Constants::interpolantModeValues[_showInterpolant];
    return;
  case SHOW_NEW:
    str << boolToOnOff(_showNew);
    return;
  case SHOW_NEW_PROPOSITIONAL:
    str << boolToOnOff(_showNewPropositional);
    return;
  case SHOW_NONCONSTANT_SKOLEM_FUNCTION_TRACE:
    str << boolToOnOff(_showNonconstantSkolemFunctionTrace);
    return;
  case SHOW_OPTIONS:
    str << boolToOnOff(_showOptions);
    return;
  case SHOW_PASSIVE:
    str << boolToOnOff(_showPassive);
    return;
  case SHOW_PREPROCESSING:
    str << boolToOnOff(_showPreprocessing);
    return;
  case SHOW_SKOLEMISATIONS:
    str << boolToOnOff(_showSkolemisations);
    return;
  case SHOW_SYMBOL_ELIMINATION:
    str << boolToOnOff(_showSymbolElimination);
    return;
  case SHOW_THEORY_AXIOMS:
    str << boolToOnOff(_showTheoryAxioms);
    return;
  case SIMULATED_TIME_LIMIT:
    str << _simulatedTimeLimit/10;
    if (_simulatedTimeLimit % 10) {
      str << '.' << _simulatedTimeLimit % 10;
    }
    return;
  case SINE_DEPTH:
    str << _sineDepth;
    return;
  case SINE_GENERALITY_THRESHOLD:
    str << _sineGeneralityThreshold;
    return;
  case SINE_SELECTION:
    str << Constants::sineSelectionValues[_sineSelection];
    return;
  case SINE_TOLERANCE:
    str << _sineTolerance;
    return;
  case SMTLIB_CONSIDER_INTS_REAL:
    str << boolToOnOff(_smtlibConsiderIntsReal);
    return;
  case SMTLIB_FLET_AS_DEFINITION:
    str << boolToOnOff(_smtlibFletAsDefinition);
    return;
  case SMTLIB_INTRODUCE_AIG_NAMES:
    str << boolToOnOff(_smtlibIntroduceAIGNames);
    return;
  case SOS:
    str << Constants::sosValues[_sos];
    return;
//  case SPLIT_ADD_GROUND_NEGATION:
//    str << boolToOnOff(_splitAddGroundNegation);
//    return;
  case SPLIT_AT_ACTIVATION:
    str << boolToOnOff(_splitAtActivation);
    return;
//  case SPLIT_GOAL_ONLY:
//    str << boolToOnOff(_splitGoalOnly);
//    return;
//  case SPLIT_INPUT_ONLY:
//    str << boolToOnOff(_splitInputOnly);
//    return;
//  case SPLIT_POSITIVE:
//    str << boolToOnOff(_splitPositive);
//    return;
  case SPLITTING:
    str << boolToOnOff(_splitting); //Constants::splittingModeValues[_splitting];
    return;
  case SSPLITTING_ADD_COMPLEMENTARY:
    str << Constants::sSplittingAddComplementaryValues[_ssplittingAddComplementary];
    return;
  case SSPLITTING_COMPONENT_SWEEPING:
    str << Constants::sSplittingComponentSweepingValues[_ssplittingComponentSweeping];
    return;
  case SSPLITTING_CONGRUENCE_CLOSURE:
    str << boolToOnOff(_ssplittingCongruenceClosure);
    return;
  case SSPLITTING_EAGER_REMOVAL:
    str << boolToOnOff(_ssplittingEagerRemoval);
    return;
  case SSPLITTING_FLUSH_PERIOD:
    str << _ssplittingFlushPeriod;
    return;
  case SSPLITTING_FLUSH_QUOTIENT:
    str << _ssplittingFlushQuotient;
    return;
  case SSPLITTING_NONSPLITTABLE_COMPONENTS:
    str << Constants::sSplittingNonsplittableComponentsValues[_ssplittingNonsplittableComponents];
    return;
  case STATISTICS:
    str << Constants::statisticsValues[_statistics];
    return;
  case SUPERPOSITION_FROM_VARIABLES:
    str << boolToOnOff(_superpositionFromVariables);
    return;
  case SYMBOL_PRECEDENCE:
    str << Constants::symbolPrecedenceValues[_symbolPrecedence];
    return;

  case TABULATION_BW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS:
    str << boolToOnOff(_tabulationBwRuleSubsumptionResolutionByLemmas);
    return;
  case TABULATION_FW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS:
    str << boolToOnOff(_tabulationFwRuleSubsumptionResolutionByLemmas);
    return;
  case TABULATION_GOAL_AWR:
    str << _tabulationGoalAgeRatio << ":" << _tabulationGoalWeightRatio;
    return;
  case TABULATION_GOAL_LEMMA_RATIO:
    str << _tabulationGoalRatio << ":" << _tabulationLemmaRatio;
    return;
  case TABULATION_INSTANTIATE_PRODUCING_RULES:
    str << boolToOnOff(_tabulationInstantiateProducingRules);
    return;
  case TABULATION_LEMMA_AWR:
    str << _tabulationLemmaAgeRatio << ":" << _tabulationLemmaWeightRatio;
    return;
  case TEST_ID:
    str << _testId;
    return;
  case THANKS:
    str << _thanks;
    return;
  case THEORY_AXIOMS:
    str << _theoryAxioms;
    return;
  case TIME_LIMIT:
    str << _timeLimitInDeciseconds/10;
    if (_timeLimitInDeciseconds % 10) {
      str << '.' << _timeLimitInDeciseconds % 10;
    }
    return;
  case TIME_LIMIT_LOCAL:
    str << _localTimeLimitInDeciseconds/10;
    if (_localTimeLimitInDeciseconds % 10) {
      str << '.' << _localTimeLimitInDeciseconds % 10;
    }
    return;
  case TIME_STATISTICS:
    str << boolToOnOff(_timeStatistics);
    return;
  case TRIVIAL_PREDICATE_REMOVAL:
    str << boolToOnOff(_trivialPredicateRemoval);
    return;

  case UNIT_RESULTING_RESOLUTION:
    str << Constants::urResolutionValues[_unitResultingResolution];
    return;
  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    str << boolToOnOff(_unusedPredicateDefinitionRemoval);
    return;

  case WEIGHT_INCREMENT:
    str << boolToOnOff(_weightIncrement);
    return;
  case WHILE_NUMBER:
    str << _whileNumber;
    return;

  case FUNCTION_NUMBER:
    str<<_functionNumber;
    return;

  case XML_OUTPUT:
    str << _xmlOutput;
    return;

#if VDEBUG
  default:
    ASS_REP(false, Constants::optionNames[optionTag]);
#endif
  }
} // Options::outputValue

/**
 * Set input file and also update problemName if it was not
 * set before
 */
void Options::setInputFile(const vstring& inputFile)
{
  CALL("Options::setInputFile");

  _inputFile = inputFile;

  if (inputFile=="") {
    return;
  }

  //update the problem name

  int length = inputFile.length() - 1;
  const char* name = inputFile.c_str();

  int b = length - 1;
  while (b >= 0 && name[b] != '/') {
    b--;
  }
  b++;

  int e = length-1;
  while (e >= b && name[e] != '.') {
    e--;
  }
  if (e < b) {
    e = length-1;
  }

  _problemName=inputFile.substr(b,e-b);
}


// /**
//  * Convert options to an XML element.
//  *
//  * @since 15/11/2004 Manchester
//  */
// XMLElement Options::toXML () const
// {
//   CALL("Options::toXML");

//   XMLElement options("options");
//   for (int i = 0;i < Constants::optionNames.length;i++) {
//     ostringstream str;
//     outputValue(str,i);
//     XMLElement option("option",true);
//     options.addChild(option);
//     option.addAttribute("name",Constants::optionNames[i]);
//     option.addAttribute("value",str.str());
//   }
//   return options;
// } // Options::toXML


/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are integers.
 *
 * @since 25/05/2004 Manchester
 */
void Options::readAgeWeightRatio(const char* val, int& ageRatio, int& weightRatio, char separator)
{
  CALL("Options::readAgeWeightRatio");

  // search the string for ":"
  bool found = false;
  int colonIndex = 0;
  while (val[colonIndex]) {
    if (val[colonIndex] == separator) {
      found = true;
      break;
    }
    colonIndex++;
  }

  if (found) {
    if (strlen(val) > 127) {
      USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
    }
    char copy[128];
    strcpy(copy,val);
    copy[colonIndex] = 0;
    int age;
    if (! Int::stringToInt(copy,age)) {
      USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
    }
    ageRatio = age;
    int weight;
    if (! Int::stringToInt(copy+colonIndex+1,weight)) {
      USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
    }
    weightRatio = weight;
    return;
  }
  ageRatio = 1;
  int weight;
  if (! Int::stringToInt(val,weight)) {
    USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
  }
  weightRatio = weight;
} // Options::readAgeWeightRatio(const char* val, int& ageRatio, int& weightRatio)


/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are integers.
 *
 * @since 25/05/2004 Manchester
 */
int Options::readTimeLimit(const char* val)
{
  CALL("Options::readTimeLimit");

  int length = strlen(val);
  if (length == 0 || length > 127) {
    USER_ERROR((vstring)"wrong value for time limit: " + val);
  }

  char copy[128];
  strcpy(copy,val);
  char* end = copy;
  // search for the end of the string for
  while (*end) {
    end++;
  }
  end--;
  float multiplier = 10.0;
  switch (*end) {
  case 's': // seconds
    multiplier = 10.0;
    *end = 0;
    break;
  case 'm': // minutes
    multiplier = 600.0;
    *end = 0;
    break;
  case 'h': // minutes
    multiplier = 36000.0;
    *end = 0;
    break;
  case 'd': // days
    multiplier = 864000.0;
    *end = 0;
    break;
  default:
    break;
  }

  float number;
  if (! Int::stringToFloat(copy,number)) {
    USER_ERROR((vstring)"wrong value for time limit: " + val);
  }

#ifdef _MSC_VER
  // Visual C++ does not know the round function
  return (int)floor(number * multiplier);
#else
  return (int)round(number * multiplier);
#endif
} // Options::readTimeLimit(const char* val)

/**
 * Read 
 */
void Options::readOptionsString(vstring testId, OptionSpecStack& assignments)
{
  CALL("Options::readOptionsString");
  cout << testId << "\n";
  while (testId != "") {
    size_t index1 = testId.find('=');
    if (index1 == vstring::npos) {
      error: USER_ERROR("bad option specification" + testId);
    }
    size_t index = testId.find(':');
    if (index!=vstring::npos && index1 > index) {
      goto error;
    }

    vstring param = testId.substr(0,index1);
    vstring value;
    if (index==vstring::npos) {
      value = testId.substr(index1+1);
    }
    else {
      value = testId.substr(index1+1,index-index1-1);
    }
    assignments.push(OptionSpec(param, value));

    if (index==vstring::npos) {
      break;
    }
    testId = testId.substr(index+1);
  }
}

/**
 * Assign option values as encoded in the option vstring.
 * according to the argument in the format
 * opt1=val1:opt2=val2:...:optn=valN,
 * for example bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none
 */
void Options::readOptionsString(vstring optionsString)
{
  CALL("Options::readOptionsString");

  // repeatedly look for param=value
  while (optionsString != "") {
    size_t index1 = optionsString.find('=');
    if (index1 == vstring::npos) {
      error: USER_ERROR("bad option specification" + optionsString);
    }
    size_t index = optionsString.find(':');
    if (index!=vstring::npos && index1 > index) {
      goto error;
    }

    vstring param = optionsString.substr(0,index1);
    vstring value;
    if (index==vstring::npos) {
      value = optionsString.substr(index1+1);
    }
    else {
      value = optionsString.substr(index1+1,index-index1-1);
    }
    setShort(param.c_str(),value.c_str());

    if (index==vstring::npos) {
      break;
    }
    optionsString = optionsString.substr(index+1);
  }
} // readOptionsString/1

/**
 * Build options from a Spider test id.
 * @since 30/05/2004 Manchester
 * @since 21/06/2005 Manchester time limit in the test id must be
 *        in deciseconds
 * @throws UserErrorException if the test id is incorrect
 */
void Options::readFromTestId (vstring testId)
{
  CALL("Options::readFromTestId");

  _normalize = true;
  _testId = testId;

  vstring ma(testId,0,3); // the first 3 characters
  if (ma == "dis") {
    _saturationAlgorithm = DISCOUNT;
  }
  else if (ma == "lrs") {
    _saturationAlgorithm = LRS;
  }
  else if (ma == "ott") {
    _saturationAlgorithm = OTTER;
  }
  else if (ma == "tab") {
    _saturationAlgorithm = TABULATION;
  }
  else if (ma == "ins") {
    _saturationAlgorithm = INST_GEN;
  }
  else {
    USER_ERROR("bad test id " + _testId);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == vstring::npos) { // not found
	USER_ERROR("No time limit in test id " + _testId);
  }
  vstring timeString = testId.substr(index+1);
  // Set this as local if we have more than one strategy
  // This will be useful in multi-strategy CASC mode and multi-strategy mode in general where we use decode
  // However, this means that in these modes the timeLimit must be set seperately
  // We also need multi-strategy CASC mode to create options such that env->isSingleStrategy is false here
  if(env->isSingleStrategy()){
    _timeLimitInDeciseconds = readTimeLimit(timeString.c_str()) / 10;
  }
  else{
    _localTimeLimitInDeciseconds = readTimeLimit(timeString.c_str()) / 10;
  }

  testId = testId.substr(3,index-3);
  switch (testId[0]) {
  case '+':
    testId = testId.substr(1);
    break;
  case '-':
    break;
  default:
    USER_ERROR("Expecting + or - next in test id " + _testId);
  }

  index = testId.find('_');
  int selection;
  vstring sel = testId.substr(0,index);
  Int::stringToInt(sel,selection);
  setSelection(selection);
  testId = testId.substr(index+1);

  if (testId == "") {
    USER_ERROR("Issue in test id " + _testId);
  }

  index = testId.find('_');
  vstring awr = testId.substr(0,index);
  readAgeWeightRatio(awr.c_str(), _ageRatio, _weightRatio);
  if (index==vstring::npos) {
    //there are no extra options
    return;
  }
  testId = testId.substr(index+1);
  //now read the rest of the options
  readOptionsString(testId);
} // Options::readFromTestId

void Options::setForcedOptionValues()
{
  CALL("Options::setForcedOptionValues");

  readOptionsString(_forcedOptions);
}

/**
 * Return testId vstring that represents current values of the options
 */
vstring Options::generateTestId() const
{
  CALL("Options::generateTestId");

  vostringstream res;
  //saturation algorithm
  res << ( (saturationAlgorithm()==DISCOUNT) ? "dis" : ( (saturationAlgorithm()==LRS) ? "lrs" : "ott") );

  //selection function
  res << (selection() < 0 ? "-" : "+") << abs(selection());
  res << "_";

  //age-weight ratio
  if (ageRatio()!=1) {
    res << ageRatio() << ":";
  }
  res << weightRatio();
  res << "_";

  Options def;
  //Initially contains current values. The values that we have output
  //as short options we set to default.
  Options cur=*this;
  bool first=true;
  static Set<Tag> forbidden;
  //we initialize the set if there's nothing inside
  if (forbidden.size()==0) {
    //things we output elsewhere
    forbidden.insert(SATURATION_ALGORITHM);
    forbidden.insert(SELECTION);
    forbidden.insert(AGE_WEIGHT_RATIO);
    forbidden.insert(TIME_LIMIT);

    //things we don't want to output
    forbidden.insert(MODE);
    forbidden.insert(TEST_ID);
    forbidden.insert(INCLUDE);
    forbidden.insert(PROBLEM_NAME);
    forbidden.insert(INPUT_FILE);
  }

  for (int i=0;i<Constants::shortNames.length;i++) {
    Tag t=static_cast<Tag>(Constants::shortNameIndexes[i]);
    if (forbidden.contains(t)) {
      continue;
    }
    vostringstream valCur;
    vostringstream valDef;
    cur.outputValue(valCur, t);
    def.outputValue(valDef, t);
    if (valCur.str()==valDef.str()) {
      continue;
    }
    if (!first) {
      res << ":";
    }
    else {
      first=false;
    }
    vstring name=Constants::shortNames[i];
    res << name << "=" << valCur.str();
    cur.set(name.c_str(), valDef.str().c_str(), t);
  }

  for (int i=0;i<NUMBER_OF_OPTIONS;i++) {
    Tag t=static_cast<Tag>(i);
    if (forbidden.contains(t)) {
      continue;
    }
    vostringstream valCur;
    vostringstream valDef;
    cur.outputValue(valCur, t);
    def.outputValue(valDef, t);
    if (valCur.str()==valDef.str()) {
      continue;
    }
    if (!first) {
      res << ":";
    }
    else {
      first=false;
    }
    res << Constants::optionNames[i] << "=" << valCur.str();
  }

  if (!first) {
    res << "_";
  }

  res << timeLimitInDeciseconds();
  return res.str();
}

/**
 * The standard output is suppressed if either LaTeX or XML
 * output is directed to cout.
 * @since 05/07/2004 Cork
 */
bool Options::outputSuppressed() const
{
  CALL("Options::setLrsFirstTimeCheck");

  return _xmlOutput == "on" ||
         _latexOutput == "on";
} // Output::outputSuppressed

// /**
//  * True if the options are complete.
//  * @since 28/07/2005 Manchester
//  */
// bool Options::complete() const
// {
//   CALL("Options::complete");

//   return (_equalityProxy==EP_OFF || _equalityProxy==EP_ON || _equalityProxy==EP_RSTC) &&
//          (_equalityResolutionWithDeletion != RA_ON ) &&
//          (_literalComparisonMode != LCM_REVERSE) &&
//          _selection < 20 &&
//          _selection > -20 &&
//          ! _sos &&
//          _superpositionFromVariables &&
//          ! _maxWeight &&
//          _binaryResolution &&
//          ! _forwardLiteralRewriting &&
//          ! env -> interpretedOperationsUsed &&
//          _sineSelection==SS_OFF &&
//          _saturationAlgorithm!=TABULATION &&
//          ! _forceIncompleteness;
// } // Options::complete

/**
 * True if the options are complete.
 * @since 23/07/2011 Manchester
 */
bool Options::complete(const Problem& prb) const
{
  CALL("Options::complete");

  //we did some transformation that made us lose completeness
  //(e.g. equality proxy replacing equality for reflexive predicate)
  if (prb.hadIncompleteTransformation()) {
    return false;
  }

  Property& prop = *prb.getProperty();

  ASS(&prop);

  // general properties causing incompleteness
  if (prop.hasInterpretedOperations()
      || prop.hasProp(Property::PR_HAS_INTEGERS)
      || prop.hasProp(Property::PR_HAS_REALS)
      || prop.hasProp(Property::PR_HAS_RATS)) {
    return false;
  }

  // preprocessing
  if (_sineSelection != SS_OFF) return false;

  switch (_saturationAlgorithm) {
  case TABULATION: return false;
  case INST_GEN: return true; // !!!
  default: break;
  }

  // preprocessing for resolution-based algorithms
  if (_sos != SOS_OFF) return false;
  // run-time rule causing incompleteness
  if (_forwardLiteralRewriting) return false;
  
  bool unitEquality = prop.category() == Property::UEQ;
  bool hasEquality = (prop.equalityAtoms() != 0);

  if (!unitEquality) {
    if (_selection <= -100 || _selection >= 100) return false;
    if (_literalComparisonMode == LCM_REVERSE) return false;
  }

  if (!hasEquality) {
    if (_binaryResolution) return true;
    if (!_unitResultingResolution) return false;
    // binary resolution is off
    return prop.category() == Property::HNE; // URR is complete for Horn problems
  }

  // equality problems
  switch (_equalityProxy) {
  case EP_R: return false;
  case EP_RS: return false;
  case EP_RST: return false;
  default: break;
  }
  if (!_demodulationRedundancyCheck) return false;
  if (_equalityResolutionWithDeletion) return false;
  if (!_superpositionFromVariables) return false;

  // only checking resolution rules remain
  bool pureEquality = (prop.atoms() == prop.equalityAtoms());
  if (pureEquality) return true;
  if (_binaryResolution) return true;
  if (!_unitResultingResolution) return false;
  return prop.category() == Property::HEQ;
} // Options::complete

/**
 * True if the options are complete for non-Horn problems without equality.
 * @since 02/08/2011 Wroclaw
 */
bool Options::completeForNNE() const
{
  CALL("Options::completeForNNE");

  // preprocessing
  if (_sineSelection != SS_OFF) return false;

  switch (_saturationAlgorithm) {
  case TABULATION: return false;
  case INST_GEN: return true; // !!!
  default: break;
  }

  // preprocessing for resolution-based algorithms
  if (_sos != SOS_OFF) return false;
  // run-time rule causing incompleteness
  if (_forwardLiteralRewriting) return false;
  
  if (_selection <= -100 || _selection >= 100) return false;

  return _binaryResolution;
} // Options::completeForNNE

/**
 * Check constraints necessary for options to make sense, and
 * call USER_ERROR if some are violated
 *
 * The function is called after all options are parsed.
 */
void Options::checkGlobalOptionConstraints() 
{
  if (_bfnt && !completeForNNE()) {
    USER_ERROR("The bfnt option can only be used with a strategy complete for non-Horn problems without equality");
  }
  if (_splitting && _saturationAlgorithm == INST_GEN) {
    USER_ERROR("saturation algorithm inst_gen cannot be used with sat splitting");
  }
  if (_extensionalityResolution != ER_OFF && _inequalitySplitting) {
    USER_ERROR("extensionality resolution can not be used together with inequality splitting");
  }
  //TODO:implement forbidden options
}

void Options::setMode(Mode newVal) {
  _mode = newVal;
  switch (newVal) {
  case MODE_CASC:
  case MODE_CASC_LTB:
    _outputAxiomNames = true;
    _proof = PROOF_TPTP;
    break;
  default:
    break;
  }
}
