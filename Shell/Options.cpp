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
  static const char* _splittingModeValues[];
  static const char* _fdeValues[];
  static const char* _lcmValues[];
  static const char* _satAlgValues[];
  static const char* _equalityProxyValues[];
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
  static const char* _satClauseDisposerValues[];

  static int shortNameIndexes[];

  static NameArray optionNames;
  static NameArray shortNames;
  static NameArray statisticsValues;
  static NameArray condensationValues;
  static NameArray demodulationValues;
  static NameArray subsumptionValues;
  static NameArray splittingModeValues;
  static NameArray fdeValues;
  static NameArray lcmValues;
  static NameArray satAlgValues;
  static NameArray equalityProxyValues;
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
  static NameArray satClauseDisposerValues;
}; // class Options::Constants


/** Names for all options */
const char* Options::Constants::_optionNames[] = {
  "abstraction",
  "age_weight_ratio",
  "arity_check",

  "backward_demodulation",
  "backward_subsumption",
  "backward_subsumption_resolution",
  "bdd_marking_subsumption",
  "bfnt",
  "binary_resolution",

  "color_unblocking",
  "condensation",

  "decode",
  "demodulation_redundancy_check",

  "empty_clause_subsumption",
  "epr_preserving_naming",
  "epr_preserving_skolemization",
  "epr_restoring_inlining",
  "equality_propagation",
  "equality_proxy",
  "equality_resolution_with_deletion",

  "forced_options",
  "forward_demodulation",
  "forward_literal_rewriting",
  "forward_subsumption",
  "forward_subsumption_resolution",
  "full_selection_for_sos",
  "function_definition_elimination",

  "general_splitting",
  "global_subsumption",

  "horn_revealing",

  "include",
  "increased_numeral_weight",
  "inequality_splitting",
  "input_file",
  "input_syntax",
  "inst_gen_big_restart_ratio",
  "inst_gen_resolution_ratio",
  "inst_gen_restart_period",
  "inst_gen_restart_period_quotient",
  "inst_gen_with_resolution",
  "interpreted_simplification",

  "latex_output",
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

  "name_prefix",
  "naming",
  "nongoal_weight_coefficient",
  "nonliterals_in_clause_weight",
  "normalize",

  "output_axiom_names",

  "predicate_definition_inlining",
  "predicate_definition_merging",
  "problem_name",
  "proof",
  "proof_checking",
  "propositional_to_bdd",

  "question_answering",

  "random_seed",
  "row_variable_max_length",

  "sat_clause_activity_decay",
  "sat_clause_disposer",
  "sat_learnt_minimization",
  "sat_learnt_subsumption_resolution",
  "sat_restart_fixed_count",
  "sat_restart_geometric_increase",
  "sat_restart_geometric_init",
  "sat_restart_luby_factor",
  "sat_restart_minisat_increase",
  "sat_restart_minisat_init",
  "sat_restart_strategy",
  "sat_solver_for_empty_clause",
  "sat_solver_with_naming",
  "sat_solver_with_subsumption_resolution",
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
  "show_preprocessing_formulas",
  "show_skolemisations",
  "show_symbol_elimination",
  "simulated_time_limit",
  "sine_depth",
  "sine_generality_threshold",
  "sine_selection",
  "sine_tolerance",
  "sos",
  "split_add_ground_negation",
  "split_at_activation",
  "split_goal_only",
  "split_input_only",
  "split_positive",
  "splitting",
  "splitting_with_blocking",
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
  "time_limit",
  "time_statistics",
  "trivial_predicate_removal",

  "unit_resulting_resolution",
  "unused_predicate_definition_removal",

  "weight_increment",

  "xml_output"};

/** Names for all options */
NameArray Options::Constants::optionNames(_optionNames,
					  sizeof(_optionNames)/sizeof(char*));

const char* Options::Constants::_shortNames[] = {
  "awr",
  "bd",
  "bfnt",
  "bms",
  "br",
  "bs",
  "bsr",
  "cond",
  "drc",
  "ecs",
  "ep",
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
  "igwr",
  "is",
  "l",
  "lcm",
  "lwlo",
  "m",
  "n",
  "nicw",
  "nm",
  "nwc",
  "p",
  "pc",
  "ptb",
  "s",
  "sa",
  "sac",
  "sagn",
  "sd",
  "sfv",
  "sgo",
  "sgt",
  "sio",
  "sos",
  "sp",
  "spl",
  "spo",
  "ss",
  "ssec",
  "sswn",
  "sswsr",
  "st",
  "stl",
  "swb",
  "t",
  "tbsr",
  "tfsr",
  "tgawr",
  "tglr",
  "tipr",
  "tlawr",
  "updr",
  "urr",
  "wi"};

/** Short names for all options */
NameArray Options::Constants::shortNames(_shortNames,
					  sizeof(_shortNames)/sizeof(char*));

int Options::Constants::shortNameIndexes[] = {
  AGE_WEIGHT_RATIO,
  BACKWARD_DEMODULATION,
  BFNT,
  BDD_MARKING_SUBSUMPTION,
  BINARY_RESOLUTION,
  BACKWARD_SUBSUMPTION,
  BACKWARD_SUBSUMPTION_RESOLUTION,
  CONDENSATION,
  DEMODULATION_REDUNDANCY_CHECK,
  EMPTY_CLAUSE_SUBSUMPTION,
  EQUALITY_PROXY,
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
  INST_GEN_WITH_RESOLUTION,
  INEQUALITY_SPLITTING,
  LOG_FILE,
  LITERAL_COMPARISON_MODE,
  LRS_WEIGHT_LIMIT_ONLY,
  MEMORY_LIMIT,
  NORMALIZE,
  NONLITERALS_IN_CLAUSE_WEIGHT,
  NAMING,
  NONGOAL_WEIGHT_COEFFICIENT,
  PROOF,
  PROOF_CHECKING,
  PROPOSITIONAL_TO_BDD,
  SELECTION,
  SATURATION_ALGORITHM,
  SPLIT_AT_ACTIVATION,
  SPLIT_ADD_GROUND_NEGATION,
  SINE_DEPTH,
  SUPERPOSITION_FROM_VARIABLES,
  SPLIT_GOAL_ONLY,
  SINE_GENERALITY_THRESHOLD,
  SPLIT_INPUT_ONLY,
  SOS,
  SYMBOL_PRECEDENCE,
  SPLITTING,
  SPLIT_POSITIVE,
  SINE_SELECTION,
  SAT_SOLVER_FOR_EMPTY_CLAUSE,
  SAT_SOLVER_WITH_NAMING,
  SAT_SOLVER_WITH_SUBSUMPTION_RESOLUTION,
  SINE_TOLERANCE,
  SIMULATED_TIME_LIMIT,
  SPLITTING_WITH_BLOCKING,
  TIME_LIMIT,
  TABULATION_BW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS,
  TABULATION_FW_RULE_SUBSUMPTION_RESOLUTION_BY_LEMMAS,
  TABULATION_GOAL_AWR,
  TABULATION_GOAL_LEMMA_RATIO,
  TABULATION_INSTANTIATE_PRODUCING_RULES,
  TABULATION_LEMMA_AWR,
  UNUSED_PREDICATE_DEFINITION_REMOVAL,
  UNIT_RESULTING_RESOLUTION,
  WEIGHT_INCREMENT};

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

const char* Options::Constants::_splittingModeValues[] = {
  "backtracking",
  "nobacktracking",
  "off"};
NameArray Options::Constants::splittingModeValues(_splittingModeValues,
					sizeof(_splittingModeValues)/sizeof(char*));

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
  "tptp"};
NameArray Options::Constants::inputSyntaxValues(_inputSyntaxValues,
						sizeof(_inputSyntaxValues)/sizeof(char*));

const char* Options::Constants::_modeValues[] = {
  "axiom_selection",
  "casc",
  "casc_ltb",
  "casc_simple_ltb",
  "clausify",
  "consequence_elimination",
  "grounding",
  "ltb_build",
  "ltb_solve",
  "profile",
  "program_analysis",
  "spider",
  "vampire"};
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
  "recently_learnt"};
NameArray Options::Constants::satVarSelectorValues(_satVarSelectorValues,
					  sizeof(_satVarSelectorValues)/sizeof(char*));

const char* Options::Constants::_satClauseDisposerValues[] = {
  "growing",
  "minisat"};
NameArray Options::Constants::satClauseDisposerValues(_satClauseDisposerValues,
					  sizeof(_satClauseDisposerValues)/sizeof(char*));

/**
 * Initialize options to the default values.
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()
  :
  _abstraction(false),
  _ageRatio(1),
  _weightRatio(1),
  _arityCheck(false),

  _backwardDemodulation(DEMODULATION_ALL),
  _backwardSubsumption(SUBSUMPTION_ON),
  _backwardSubsumptionResolution(SUBSUMPTION_OFF),
  _bddMarkingSubsumption(false),
  _bfnt(false),
  _binaryResolution(true),

  _colorUnblocking(false),
  _condensation(CONDENSATION_OFF),

  _demodulationRedundancyCheck(true),

  _emptyClauseSubsumption(false),
  _eprPreservingNaming(false),
  _eprPreservingSkolemization(false),
  _eprRestoringInlining(false),
  _equalityPropagation(false),
  _equalityProxy(EP_OFF),
  _equalityResolutionWithDeletion(RA_INPUT_ONLY),

  _forwardDemodulation(DEMODULATION_ALL),
  _forwardLiteralRewriting(false),
  _forwardSubsumption(true),
  _forwardSubsumptionResolution(true),
  _fullSelectionForSOS(false),
  _functionDefinitionElimination(FDE_ALL),

  _generalSplitting(RA_OFF),
  _globalSubsumption(false),

  _hornRevealing(false),

  _include(""),
  _increasedNumeralWeight(false),
  _inequalitySplitting(3),
  _inputFile(""),
  _inputSyntax(IS_TPTP),
  _instGenBigRestartRatio(0.0f),
  _instGenResolutionRatioInstGen(1),
  _instGenResolutionRatioResolution(1),
  _instGenRestartPeriod(1000),
  _instGenRestartPeriodQuotient(1.0f),
  _instGenWithResolution(false),
  _interpretedSimplification(false),

  _latexOutput("off"),
  _literalComparisonMode(LCM_STANDARD),
  _logFile("off"),
  _lrsFirstTimeCheck(5),
  _lrsWeightLimitOnly(false),

  _maxActive(0),
  _maxAnswers(1),
  _maxInferenceDepth(0),
  _maxPassive(0),
  _maxWeight(0),
#if VDEBUG
  _memoryLimit(1000),
#else
  _memoryLimit(3000),
#endif
  _mode(MODE_VAMPIRE),

  _namePrefix(""),
  _naming(8),

  _nongoalWeightCoefficient(1.0),
  _nonliteralsInClauseWeight(false),
  _normalize(false),

  _outputAxiomNames(false),

  _predicateDefinitionInlining(INL_OFF),
  _predicateDefinitionMerging(false),
  _problemName("unknown"),
  _proof(PROOF_ON),
  _proofChecking(false),
  _propositionalToBDD(true),

  _questionAnswering(QA_OFF),

  _randomSeed(Random::seed()),
  _rowVariableMaxLength(2),

  _satClauseActivityDecay(1.001f),
  _satClauseDisposer(SCD_MINISAT),
  _satLearntMinimization(true),
  _satLearntSubsumptionResolution(true),
  _satRestartFixedCount(16000),
  _satRestartGeometricIncrease(1.1f),
  _satRestartGeometricInit(32),
  _satRestartLubyFactor(100),
  _satRestartMinisatIncrease(1.1f),
  _satRestartMinisatInit(100),
  _satRestartStrategy(SRS_LUBY),
  _satSolverForEmptyClause(true),
  _satSolverWithNaming(false),
  _satSolverWithSubsumptionResolution(false),
  _satVarActivityDecay(1.05f),
  _satVarSelector(SVS_ACTIVE),
  _saturationAlgorithm(LRS),
  _selection(10),
  _showActive(false),
  _showBlocked(false),
  _showDefinitions(false),
  _showInterpolant(INTERP_OFF),
  _showNew(false),
  _showNewPropositional(false),
  _showNonconstantSkolemFunctionTrace(false),
  _showOptions(false),
  _showPassive(false),
  _showPreprocessingFormulas(false),
  _showSkolemisations(false),
  _showSymbolElimination(false),
  _simulatedTimeLimit(0),
  _sineDepth(0),
  _sineGeneralityThreshold(0),
  _sineSelection(SS_OFF),
  _sineTolerance(1.0f),
  _sos(false),
  _splitAddGroundNegation(true),
  _splitAtActivation(false),
  _splitGoalOnly(false),
  _splitInputOnly(true),
  _splitPositive(false),
  _splitting(SM_NOBACKTRACKING),
  _splittingWithBlocking(false),
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
  _timeLimitInDeciseconds(600),
  _timeStatistics(false),
  _trivialPredicateRemoval(false),

  _unitResultingResolution(false),
  _unusedPredicateDefinitionRemoval(true),

  _weightIncrement(false),

  _xmlOutput("off"),

  _nonGoalWeightCoeffitientNumerator(1),
  _nonGoalWeightCoeffitientDenominator(1),
  _forceIncompleteness(false)
{
  CALL("Options::Options");
} // Options::Options


/**
 * Set option by its name and value.
 * @since 13/11/2004 Manchester
 */
void Options::set(const char* name,const char* value)
{
  CALL ("Options::set/2");

  try{
    set(name,value,Constants::optionNames.find(name));
  }
  catch(ValueNotFoundException) {
    USER_ERROR((string)name + " is not a valid option");
  }
} // Options::set/2


/**
 * Set option by its name and value.
 * @since 06/04/2005 Torrevieja
 */
void Options::set(const string& name,const string& value)
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
    case ABSTRACTION:
      _abstraction = onOffToBool(value,name);
      return;
    case AGE_WEIGHT_RATIO:
      readAgeWeightRatio(value, _ageRatio, _weightRatio);
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
    case BDD_MARKING_SUBSUMPTION:
      _bddMarkingSubsumption = onOffToBool(value,name);
      return;
    case BFNT:
      _bfnt = onOffToBool(value,name);
      return;
    case BINARY_RESOLUTION:
      _binaryResolution = onOffToBool(value,name);
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

    case EMPTY_CLAUSE_SUBSUMPTION:
      _emptyClauseSubsumption = onOffToBool(value,name);
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
      if(_equalityResolutionWithDeletion==RA_ON) {
	USER_ERROR("equality_resolution_with_deletion is not implemented for value \"on\"");
      }
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
    case FULL_SELECTION_FOR_SOS:
      _fullSelectionForSOS = onOffToBool(value,name);
      return;
    case FUNCTION_DEFINITION_ELIMINATION:
      _functionDefinitionElimination =
	(FunctionDefinitionElimination)Constants::fdeValues.find(value);
      return;

    case GENERAL_SPLITTING:
      _generalSplitting = (RuleActivity)Constants::ruleActivityValues.find(value);
      if(_generalSplitting==RA_ON) {
	USER_ERROR("general_splitting is not implemented for value \"on\"");
      }
      return;
    case GLOBAL_SUBSUMPTION:
      _globalSubsumption = onOffToBool(value,name);
      return;

    case HORN_REVEALING:
      _hornRevealing = onOffToBool(value,name);
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
	if(floatValue<0.0f || floatValue>1.0f) {
	  USER_ERROR("inst_gen_big_restart_ratio must be a number between 0 and 1 (inclusive)");
	}
	_instGenBigRestartRatio = floatValue;
	return;
      }
      break;
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
	if(floatValue<1.0f) {
	  USER_ERROR("inst_gen_restart_period_quotient must be a number at least 1");
	}
	_instGenRestartPeriodQuotient = floatValue;
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
    case PROOF:
      _proof = (Proof)Constants::proofValues.find(value);
      return;
    case PROOF_CHECKING:
      _proofChecking = onOffToBool(value,name);
      return;
    case PROPOSITIONAL_TO_BDD:
      _propositionalToBDD = onOffToBool(value,name);
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
	if(floatValue<=1.0f) {
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
    case SAT_RESTART_FIXED_COUNT:
      if (Int::stringToUnsignedInt(value,unsignedValue)) {
	_satRestartFixedCount = unsignedValue;
	return;
      }
      break;
    case SAT_RESTART_GEOMETRIC_INCREASE:
      if (Int::stringToFloat(value,floatValue)) {
	if(floatValue<=1.0f) {
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
	if(floatValue<=1.0f) {
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
    case SAT_SOLVER_FOR_EMPTY_CLAUSE:
      _satSolverForEmptyClause = onOffToBool(value,name);
      return;
    case SAT_SOLVER_WITH_NAMING:
      _satSolverWithNaming = onOffToBool(value,name);
      return;
    case SAT_SOLVER_WITH_SUBSUMPTION_RESOLUTION:
      _satSolverWithSubsumptionResolution = onOffToBool(value,name);
      return;
    case SAT_VAR_ACTIVITY_DECAY:
      if (Int::stringToFloat(value,floatValue)) {
	if(floatValue<=1.0f) {
	  USER_ERROR("sat_var_activity_decay must be a number greater than 1");
	}
	_satVarActivityDecay = floatValue;
	return;
      }
      break;
    case SAT_VAR_SELETOR:
      _satVarSelector = (SatVarSelector)Constants::satVarSelectorValues.find(value);
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
    case SHOW_PREPROCESSING_FORMULAS:
      _showPreprocessingFormulas = onOffToBool(value,name);
      return;
    case SHOW_SKOLEMISATIONS:
      _showSkolemisations = onOffToBool(value,name);
      return;
    case SHOW_SYMBOL_ELIMINATION:
      _showSymbolElimination = onOffToBool(value,name);
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
      if(!Int::stringToFloat(value,floatValue) || (floatValue!=0.0f && floatValue<1.0f)) {
	USER_ERROR("sine_tolerance value must be a float number greater than or equal to 1");
      }
      _sineTolerance = floatValue;
      return;
    case SOS:
      _sos = onOffToBool(value,name);
      return;
    case SPLIT_ADD_GROUND_NEGATION:
      _splitAddGroundNegation = onOffToBool(value,name);
      return;
    case SPLIT_AT_ACTIVATION:
      _splitAtActivation = onOffToBool(value,name);
      return;
    case SPLIT_GOAL_ONLY:
      _splitGoalOnly = onOffToBool(value,name);
      return;
    case SPLIT_INPUT_ONLY:
      _splitInputOnly = onOffToBool(value,name);
      return;
    case SPLIT_POSITIVE:
      _splitPositive = onOffToBool(value,name);
      return;
    case SPLITTING:
      _splitting = (SplittingMode)Constants::splittingModeValues.find(value);
      return;
    case SPLITTING_WITH_BLOCKING:
      _splittingWithBlocking = onOffToBool(value,name);
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
    case TIME_LIMIT:
      _timeLimitInDeciseconds = readTimeLimit(value);
      return;
    case TIME_STATISTICS:
      _timeStatistics = onOffToBool(value,name);
      return;
    case TRIVIAL_PREDICATE_REMOVAL:
      _trivialPredicateRemoval = onOffToBool(value,name);
      return;

    case UNIT_RESULTING_RESOLUTION:
      _unitResultingResolution = onOffToBool(value,name);
      return;
    case UNUSED_PREDICATE_DEFINITION_REMOVAL:
      _unusedPredicateDefinitionRemoval = onOffToBool(value,name);
      return;

    case WEIGHT_INCREMENT:
      _weightIncrement = onOffToBool(value,name);
      return;

    case XML_OUTPUT:
      _xmlOutput = value;
      return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
    throw ValueNotFoundException();
  }
  catch(ValueNotFoundException) {
    USER_ERROR((string)"wrong value (" + value + ") for " + name);
  }

} // Options::set


/**
 * Set option by its short name and value. If such a short name does not
 * exist, try to use the long name instead.
 *
 * @since 21/11/2004 Manchester
 */
void Options::setShort(const char* name,const char* value)
{
  CALL ("Options::setShort");

  int found;
  try {
    found = Constants::shortNameIndexes[Constants::shortNames.find(name)];
  }
  catch(ValueNotFoundException) {
    try {
      found = Constants::optionNames.find(name);
    }
    catch(ValueNotFoundException) {
      USER_ERROR((string)name + " is not a valid option");
    }
  }

  set(name,value,found);
} // Options::setShort


/**
 * Convert the string onOff to a boolean value. If onOff is not one
 * of "on" or "off", then raise a user error exception.
 * @since 15/11/2004 Manchester
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

  USER_ERROR((string)"wrong value for " + option + ": " + onOff);
} // Options::onOffToBool


/**
 * Convert a boolean value to the corresponding string "on"/"off"
 * value.
 * @since 15/11/2004 Manchester
 */
string Options::boolToOnOff (bool val)
{
  CALL("Options::boolToOnOff");

  static string on ("on");
  static string off ("off");

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
 * @since 16/10/2003 Manchester, relativeName change to string from char*
 */
string Options::includeFileName (const string& relativeName)
{
  CALL("Options::includeFileName");

  if (relativeName[0] == '/') { // absolute name
    return relativeName;
  }

  if(System::fileExists(relativeName)) {
    return relativeName;
  }

  // truncatedRelativeName is relative.
  // Use the conventions of Vampire:
  // (a) first search the value of "include"
  string dir = include();
  if (dir == "") { // include undefined
    // (b) search the value of the environment variable TPTP_DIR
    char* env = getenv("TPTP");
    if (env) {
      dir = env;
    }
    else {
      dir = ".";
    }
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
  case ABSTRACTION:
    str << boolToOnOff(_abstraction);
    return;
  case AGE_WEIGHT_RATIO:
    str << _ageRatio << ':' << _weightRatio;
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
  case BDD_MARKING_SUBSUMPTION:
    str << boolToOnOff(_bddMarkingSubsumption);
    return;
  case BFNT:
    str << boolToOnOff(_bfnt);
    return;
  case BINARY_RESOLUTION:
    str << boolToOnOff(_binaryResolution);
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

  case EMPTY_CLAUSE_SUBSUMPTION:
    str << boolToOnOff(_emptyClauseSubsumption);
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
  case FULL_SELECTION_FOR_SOS:
    str << boolToOnOff(_fullSelectionForSOS);
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
  case INST_GEN_RESOLUTION_RATIO:
    str << _instGenResolutionRatioInstGen << ':' << _instGenResolutionRatioResolution;
    return;
  case INST_GEN_RESTART_PERIOD:
    str << _instGenRestartPeriod;
    return;
  case INST_GEN_RESTART_PERIOD_QUOTIENT:
    str << _instGenRestartPeriodQuotient;
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
  case PROBLEM_NAME:
    str << _problemName;
    return;
  case PROOF:
    str << boolToOnOff(_proof);
    return;
  case PROOF_CHECKING:
    str << boolToOnOff(_proofChecking);
    return;
  case PROPOSITIONAL_TO_BDD:
    str << boolToOnOff(_propositionalToBDD);
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
  case SAT_SOLVER_FOR_EMPTY_CLAUSE:
    str << boolToOnOff(_satSolverForEmptyClause);
    return;
  case SAT_SOLVER_WITH_NAMING:
    str << boolToOnOff(_satSolverWithNaming);
    return;
  case SAT_SOLVER_WITH_SUBSUMPTION_RESOLUTION:
    str << boolToOnOff(_satSolverWithSubsumptionResolution);
    return;
  case SAT_VAR_ACTIVITY_DECAY:
    str << _satVarActivityDecay;
    return;
  case SAT_VAR_SELETOR:
    str << Constants::satVarSelectorValues[_satVarSelector];
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
  case SHOW_PREPROCESSING_FORMULAS:
    str << boolToOnOff(_showPreprocessingFormulas);
    return;
  case SHOW_SKOLEMISATIONS:
    str << boolToOnOff(_showSkolemisations);
    return;
  case SHOW_SYMBOL_ELIMINATION:
    str << boolToOnOff(_showSymbolElimination);
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
  case SOS:
    str << boolToOnOff(_sos);
    return;
  case SPLIT_ADD_GROUND_NEGATION:
    str << boolToOnOff(_splitAddGroundNegation);
    return;
  case SPLIT_AT_ACTIVATION:
    str << boolToOnOff(_splitAtActivation);
    return;
  case SPLIT_GOAL_ONLY:
    str << boolToOnOff(_splitGoalOnly);
    return;
  case SPLIT_INPUT_ONLY:
    str << boolToOnOff(_splitInputOnly);
    return;
  case SPLIT_POSITIVE:
    str << boolToOnOff(_splitPositive);
    return;
  case SPLITTING:
    str << Constants::splittingModeValues[_splitting];
    return;
  case SPLITTING_WITH_BLOCKING:
    str << boolToOnOff(_splittingWithBlocking);
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
  case TIME_LIMIT:
    str << _timeLimitInDeciseconds/10;
    if (_timeLimitInDeciseconds % 10) {
      str << '.' << _timeLimitInDeciseconds % 10;
    }
    return;
  case TIME_STATISTICS:
    str << boolToOnOff(_timeStatistics);
    return;
  case TRIVIAL_PREDICATE_REMOVAL:
    str << boolToOnOff(_trivialPredicateRemoval);
    return;

  case UNIT_RESULTING_RESOLUTION:
    str << boolToOnOff(_unitResultingResolution);
    return;
  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    str << boolToOnOff(_unusedPredicateDefinitionRemoval);
    return;

  case WEIGHT_INCREMENT:
    str << boolToOnOff(_weightIncrement);
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
 * Return the problem name
 *
 * The problem name is computed from the input file name in
 * the @b setInputFile function. If the input file is not set,
 * the problem name is equal to "unknown".
 *
 */
string Options::problemName () const
{
  //Tracing removed as this function is called by assertion
  //violation reporting and it influenced the output.
//  CALL("Options::problemName");

  return _problemName;
} // const char* Options::problemName () const

/**
 * Set input file and also update problemName if it was not
 * set before
 */
void Options::setInputFile(const string& inputFile)
{
  CALL("Options::setInputFile");

  _inputFile = inputFile;

  if(inputFile=="") {
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
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    char copy[128];
    strcpy(copy,val);
    copy[colonIndex] = 0;
    int age;
    if (! Int::stringToInt(copy,age)) {
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    ageRatio = age;
    int weight;
    if (! Int::stringToInt(copy+colonIndex+1,weight)) {
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    weightRatio = weight;
    return;
  }
  ageRatio = 1;
  int weight;
  if (! Int::stringToInt(val,weight)) {
    USER_ERROR((string)"wrong value for age-weight ratio: " + val);
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
    USER_ERROR((string)"wrong value for time limit: " + val);
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
    USER_ERROR((string)"wrong value for time limit: " + val);
  }

#ifdef _MSC_VER
  // Visual C++ does not know the round function
  return (int)floor(number * multiplier);
#else
  return (int)round(number * multiplier);
#endif
} // Options::readTimeLimit(const char* val)


/**
 * Assign option values according to the argument in the format
 * <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN>
 */
void Options::readOptionsString(string testId)
{
  CALL("Options::readOptionsString");

  // repeatedly look for param=value
  while (testId != "") {
    size_t index1 = testId.find('=');
    if (index1 == string::npos) {
      error: USER_ERROR("bad option specification" + testId);
    }
    size_t index = testId.find(':');
    if (index!=string::npos && index1 > index) {
      goto error;
    }

    string param = testId.substr(0,index1);
    string value;
    if(index==string::npos) {
      value = testId.substr(index1+1);
    }
    else {
      value = testId.substr(index1+1,index-index1-1);
    }
    setShort(param.c_str(),value.c_str());

    if(index==string::npos) {
      break;
    }
    testId = testId.substr(index+1);
  }
}

/**
 * Build options from a Spider test id.
 * @since 30/05/2004 Manchester
 * @since 21/06/2005 Manchester time limit in the test id must be
 *        in deciseconds
 * @throws UserErrorException if the test id is incorrect
 */
void Options::readFromTestId (string testId)
{
  CALL("Options::readFromTestId");

  _normalize = true;
  _testId = testId;

  string ma(testId,0,3); // the first 3 characters
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
  error: USER_ERROR("bad test id " + _testId);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == string::npos) { // not found
    goto error;
  }
  string timeString = testId.substr(index+1);
  _timeLimitInDeciseconds = readTimeLimit(timeString.c_str()) / 10;

  testId = testId.substr(3,index-3);
  switch (testId[0]) {
  case '+':
    testId = testId.substr(1);
    break;
  case '-':
    break;
  default:
    goto error;
  }

  index = testId.find('_');
  int selection;
  string sel = testId.substr(0,index);
  Int::stringToInt(sel,selection);
  setSelection(selection);
  testId = testId.substr(index+1);

  if (testId == "") {
    goto error;
  }

  index = testId.find('_');
  string awr = testId.substr(0,index);
  readAgeWeightRatio(awr.c_str(), _ageRatio, _weightRatio);
  if(index==string::npos) {
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
 * Return testId string that represents current values of the options
 */
string Options::generateTestId() const
{
  CALL("Options::generateTestId");

  stringstream res;

  //saturation algorithm
  res<<( (saturationAlgorithm()==DISCOUNT) ? "dis" : ( (saturationAlgorithm()==LRS) ? "lrs" : "ott") );

  //selection function
  res<< ( (selection()<0) ? "-" : "+" ) << abs(selection());
  res<<"_";

  //age-weight ratio
  if(ageRatio()!=1) {
    res<<ageRatio()<<":";
  }
  res<<weightRatio();
  res<<"_";

  Options def;
  //Initially contains current values. The values that we have output
  //as short options we set to default.
  Options cur=*this;

  bool first=true;

  static Set<Tag> forbidden;
  //we initialize the set if there's nothing inside
  if(forbidden.size()==0) {
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

  for(int i=0;i<Constants::shortNames.length;i++) {
    Tag t=static_cast<Tag>(Constants::shortNameIndexes[i]);
    if(forbidden.contains(t)) {
      continue;
    }
    stringstream valCur;
    stringstream valDef;
    cur.outputValue(valCur, t);
    def.outputValue(valDef, t);
    if(valCur.str()==valDef.str()) {
      continue;
    }
    if(!first) {
      res<<":";
    }
    else {
      first=false;
    }
    string name=Constants::shortNames[i];
    res<<name<<"="<<valCur.str();
    cur.set(name.c_str(), valDef.str().c_str(), t);
  }

  for(int i=0;i<NUMBER_OF_OPTIONS;i++) {
    Tag t=static_cast<Tag>(i);
    if(forbidden.contains(t)) {
      continue;
    }
    stringstream valCur;
    stringstream valDef;
    cur.outputValue(valCur, t);
    def.outputValue(valDef, t);
    if(valCur.str()==valDef.str()) {
      continue;
    }
    if(!first) {
      res<<":";
    }
    else {
      first=false;
    }
    res<<Constants::optionNames[i]<<"="<<valCur.str();
  }

  if(!first) {
    res<<"_";
  }

  res<<timeLimitInDeciseconds();
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
//          ! env.interpretedOperationsUsed &&
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
  if(prb.hadIncompleteTransformation()) {
    return false;
  }

  Property& prop = *prb.getProperty();

  ASS(&prop);

  // general properties causing incompleteness
  // if (prop.usesIntegers()) return false;

  // preprocessing
  if (_sineSelection != SS_OFF) return false;

  switch (_saturationAlgorithm) {
  case TABULATION: return false;
  case INST_GEN: return true; // !!!
  default: break;
  }

  // preprocessing for resolution-based algorithms
  if (_sos) return false;
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
  if (_sos) return false;
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
void Options::checkGlobalOptionConstraints() const
{
  if(satSolverForEmptyClause() && emptyClauseSubsumption()) {
    USER_ERROR("Empty clause subsumption cannot be performed when SAT solver is used for handling empty clauses");
  }
  if(!propositionalToBDD() && bddMarkingSubsumption()) {
    USER_ERROR("BDD marking subsumption cannot be used without BDDs enabled (the \"propositional_to_bdd\" option)");
  }
  if(propositionalToBDD() && splittingWithBlocking()) {
    USER_ERROR("Splitting with blocking cannot be used with BDDs enabled (the \"propositional_to_bdd\" option)");
  }
  if(splitting()!=SM_NOBACKTRACKING && splittingWithBlocking()) {
    USER_ERROR("Splitting with blocking can be used only with splitting without backtracking");
  }
  if(splitting()==SM_BACKTRACKING && propositionalToBDD()) {
    USER_ERROR("Backtracking splitting cannot be used unless all BDD related options are disabled");
  }
  if(showInterpolant()!=INTERP_OFF && splitting()==SM_BACKTRACKING) {
    USER_ERROR("Cannot output interpolant with backtracking splitting");
  }
  if (_bfnt && !completeForNNE()) {
    USER_ERROR("The bfnt option can only be used with a strategy complete for non-Horn problems without equality");
  }
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
