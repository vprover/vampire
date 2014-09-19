/**
 * @file Options.cpp
 * Implements Vampire options.
 *
 * @since 06/06/2001 Manchester, completely rewritten
 *
 * @since Sep 14 rewritten by Giles
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
#include "Lib/OptionNameArray.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/System.hpp"

#include "Kernel/Problem.hpp"

#include "Options.hpp"
#include "Property.hpp"

using namespace Lib;
using namespace Shell;


/**
 * Initialize options to the default values.
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()
:
// not sure where these are set or what they control
_backjumpTargetIsDecisionPoint(true),
_bpCollapsingPropagation(false),
_equivalentVariableRemoval(true),
_forceIncompleteness(false),
_maximalPropagatedEqualityLength(5),

// will be set in setNongoalWeightCoefficient anyway
_nonGoalWeightCoeffitientDenominator(1),
_nonGoalWeightCoeffitientNumerator(1),

// not sure where these are set or what they control
_selectUnusedVariablesFirst(false),
_updatesByOneConstraint(3)

{
    CALL("Options::Options");
    
   
    _ageWeightRatio = RatioOptionValue("age_weight_ratio","awr");
    _ageWeightRatio.description=
             "Ratio in which clauses are being selected for activation i.e. a:w means that for every a clauses selected based on age"
             "there will be w selected based on weight.";
    _ageWeightRatio.defaultValue=1;
    _ageWeightRatio.defaultOtherValue=1;
    lookup.insert(_ageWeightRatio);
    
    _aigBddSweeping = BoolOptionValue("aig_bdd_sweeping","");
    _aigBddSweeping.description="";
    _aigBddSweeping.defaultValue=false;
    lookup.insert(_aigBddSweeping);
    
    _aigConditionalRewriting = BoolOptionValue("aig_conditional_rewriting","");
    _aigConditionalRewriting.description="";
    _aigConditionalRewriting.defaultValue=false;
    lookup.insert(_aigConditionalRewriting);
    
    _aigDefinitionIntroduction = BoolOptionValue("aig_definition_introduction","");
    _aigDefinitionIntroduction.description="";
    _aigDefinitionIntroduction.defaultValue=false;
    lookup.insert(_aigDefinitionIntroduction);
    
    _aigDefinitionIntroductionThreshold = UnsignedOptionValue("aig_definition_introduction_threshold","");
    _aigDefinitionIntroductionThreshold.description=
               "number of subformula occurrences needed to introduce a name for it (if aig_definition_introduction is enabled)";
    _aigDefinitionIntroductionThreshold.defaultValue=4;
    lookup.insert(_aigDefinitionIntroductionThreshold);

    _aigFormulaSharing = BoolOptionValue("aig_formula_sharing","");
    _aigFormulaSharing.description="Detection and sharing of common subformulas using AIG representation";
    _aigFormulaSharing.defaultValue=false;
    lookup.insert(_aigFormulaSharing);
    
    _aigInliner = BoolOptionValue("aig_inliner","");
    _aigInliner.description="";
    _aigInliner.defaultValue=false;
    lookup.insert(_aigInliner);
    
    _arityCheck = BoolOptionValue("arity_check","");
    _arityCheck.description="The same symbol name cannot be used with multiple arities";
    _arityCheck.defaultValue=false;
    lookup.insert(_arityCheck);
    
    // backwardTargetIsDecsisionPoint
    
    _backwardDemodulation = OptionValue<Demodulation>("backward_demodulation","bd");
    _backwardDemodulation.description=
             "Oriented rewriting of kept clauses by newly derived unit equalities\n"
             "s = t     L[sθ] \\/ C\n"
             "---------------------   where sθ > tθ (replaces RHS)\n"
             " L[tθ] \\/ C\n";
    _backwardDemodulation.setOptionValues(OptionValues("all","off","preordered"));
    _backwardDemodulation.defaultValue= DEMODULATION_ALL;
    lookup.insert(_backwardDemodulation);
    
    _backwardSubsumption = OptionValue<Subsumption>("backward_subsumption");
    _backwardSubsumption.descripttion=
             "unit_only means that the subsumption will be performed only by unit clauses";
    _backwardSubsumption.setOptionValues(OptionValues("off","on","unit_only"));
    _backwardSubsumption.defaultValue=SUBSUMPTION_ON;
    lookup.insert(_backwardSubsumption);
    
    _backwardSubsumptionResolution = OptionValue<Subsumption>("backward_subsumption_resolution","bsr");
    _backwardSubsumptionResolution.description=
             "unit_only means that the subsumption resolution will be performed only by unit clauses";
    _backwardSubsumptionResolution.setOptionValues(OptionValues("off","on","unit_only"));
    _backwardSubsumptionResolution.defaultValue=SUBSUMPTION_OFF;
    lookup.insert(_backwardSubsumptionResolution);
    
    _bfnt = BoolOptionValue("bfnt","bfnt");
    _bfnt.description="";
    _bfnt.defaultValue=false;
    lookup.insert(_bfnt);

    _binaryResolution = BoolOptionValue("binary_resolution","br");
    _binaryResolution.description="";
    _binaryResolution.defaultValue=true;
    lookup.insert(_binaryResolution);

    _bpCollapsingPropagation = BoolOptionValue("bp_add_collapsing_inequalities","");
    _bpCollapsingPropagation.description="";
    //__bpCollapsingPropagation.defaultValue // no default?
    lookup.insert(_bpCollapsingPropagation);

    _bpAllowedFMBalance = UnsignedOptionValue("bp_allowed_fm_balance","");
    _bpAllowedFMBalance.description="";
    _bpAllowedFMBalance.defaultValue=0;
    lookup.insert(_bpAllowedFMBalance);

    _bpAlmostHalfBoundingRemoval= OptionValue<BPAlmostHalfBoundingRemoval>("bp_almost_half_bounding_removal","");
    _bpAlmostHalfBoundingRemoval.description="";
    _bpAlmostHalfBoundingRemoval.setOptionValues(OptionValues("bounds_on","off","on"));
    _bpAlmostHalfBoundingRemoval.defaultValue=ON;
    lookup.insert(_bpAlmostHalfBoundingRemoval);

    _bpAssignmentSelector = OptionValue<BPAssignmentSelector>("bp_assignment_selector","");
    _bpAssignmentSelector.description="";
    _bpAssignmentSelector.setOptionValues(OptionValues("alternating","bmp","lower_bound";
                                                       "middle","random","rational","smallest";
                                                       "tight","tightish","upper_bound"));
    _bpAssignmentSelectordefaultValue=RANDOM;
    lookup.insert(_bpAssignmentSelector)
    
    _updatesByOneConstraint= OptionValue("bp_bound_improvement_limit","");
    _updatesByOneConstraint.description="";
    //_updatesByOneConstraint.defaultValue // no default?
    lookup.insert(_updatesByOneConstraint);

    _bpConflictSelector = OptionValue<BPConflictSelector>("bp_conflict_selector","");
    _bpConflictSelector.description="";
    _bpConflictSelector.setOptionValues(OptionValues("least_recent","most_recent","shortest"));
    _bpConflictSelector.defaultValue=MOST_RECENT;
    lookup.insert(_bpConflictSelector)

    _bpConservativeAssignmentSelection = BoolOptionValue("bp_conservative_assignment_selection","");
    _bpConservativeAssignmentSelection.description="";
    _bpConservativeAssignmentSelection.defaultValue=true;
    lookup.insert(_bpConservativeAssignmentSelection);

    _bpFmElimination= BoolOptionValue("bp_fm_elimination","");
    _bpFmElimination.description="";
    _bpFmElimination.defaultValue=true;
    lookup.insert(_bpFmElimination);

    _maximalPropagatedEqualityLength = UnsignedOptionValue("bp_max_prop_length","");
    _maximalPropagatedEqualityLength.description="";
    //_maximalPropagatedEqualityLength.defaultValue // no default?
    lookup.insert(_maximalPropagatedEqualityLength);

    _bpPropagateAfterConflict = BoolOptionValue("bp_propagate_after_conflict","");
    _bpPropagateAfterConflict.description="";
    _bpPropagateAfterConflict.defaultValue=true;
    lookup.insert(_bpPropagateAfterConflict);

    _bpStartWithPrecise = BoolOptionValue("bp_start_with_precise","");
    _bpStartWithPrecise.description="";
    _bpStartWithPrecise.defaultValue=false;
    lookup.insert(_bpStartWithPrecise);

    _bpStartWithRational = BoolOptionValue("bp_start_with_rational","");
    _bpStartWithRational.description="";
    _bpStartWithRational.defaultValue=false;
    lookup.insert(_bpStartWithRational);

    _bpVariableSelector = OptionValue<BPVariableSelector>("bp_variable_selector","");
    _bpVariableSelector.description="";
    _bpVariableSelector.setOptionValues(OptionValues("conflicting","conflicting_and_collapsing";
                                                     "first","look_ahead","random","recent_collapsing";
                                                     "recent_conflicting","tightest_bound"));
    _bpVariableSelector.defaultValue=TIGHTEST_BOUND;
    lookup.insert(_bpVariableSelector);
    
    _colorUnblocking = BoolOptionValue("color_unblocking","");
    _colorUnblocking.description="";
    _colorUnblocking.defaultValue=false;
    lookup.insert(_colorUnblocking);

    _condensation = OptionValue<Condensation>("condensation","cond");
    _condensation.description=
             "If 'fast' is specified, we only perform condensations that are easy to check for.";
    _condensation.setOptionValues(OptionValues("fast","off","on"));
    _condensation.defaultValue=OFF;
    lookup.insert(_condensation);


    _decode = StringOptionValue("decode","");
    _decode.description="";
    _decode.defaultValue="";
    lookup.insert(_decode);

    _demodulationRedundancyCheck = BoolOptionValue("demodulation_redundancy_check","drc");
    _demodulationRedundancyCheck.description=
             "Avoids the following cases of backward and forward demodulation, as they do not preserve completeness:\n"
             "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n"

             "--------------------- \t ---------------------\n" 
             "t = t1 \\/ C \t\t t != t1 \\/ C\n"
             "where t > t1 and s = t > C (RHS replaced)";
    _demodulationRedundancyCheck.defaultValue=true;
    lookup.insert(_demodulationRedundancyCheck);

    _distinctProcessor = BoolOptionValue("distinct_processor","");
    _distinctProcessor.description="handles $distinct predicates";
    _distinctProcessor.defaultValue=false;
    lookup.insert(_distinctProcessor);

    _eprPreservingNaming = BoolOptionValue("epr_preserving_naming","");
    _eprPreservingNaming.description=
             "Naming will not cause introduction of any non-constant functions."
             "The nonconstant functions can be introduced by naming in a name definition when a universal quantifier turns into an existential one and is skolemized.";
    _eprPreservingNaming.defaultValue=false;
    lookup.insert(_eprPreservingNaming);

    _eprPreservingSkolemization= BoolOptionValue("epr_preserving_skolemization","");
    _eprPreservingSkolemization.description="";
    _eprPreservingSkolemization.defaultValue=false;
    lookup.insert(_eprPreservingSkolemization);

    _eprRestoringInlining= BoolOptionValue("epr_restoring_inlining","");
    _eprRestoringInlining.description="";
    _eprRestoringInlining.defaultValue=false;
    lookup.insert(_eprRestoringInlining);

    _equalityPropagation = BoolOptionValue("equality_propagation","");
    _equalityPropagation.description=
             "propagate equalities in formulas, for example\n"
             "X=Y => X=f(Y) ---> X=f(X)\n"
             "Such propagation can simplify formulas early in the preprocessing and so help other preprocessing rules (namely dealing with predicate definitions).";
    _equalityPropagation.defaultValue=false;
    lookup.insert(_equalityPropagation);

    _equalityProxy = OptionValue<EqualityProxy>( "equality_proxy","ep");
    _equalityProxy.description="";
    _equalityProxy.setOptionValues(OptionValues("R","RS","RST","RSTC","off"));
    _equalityProxy.defaultValue=OFF;
    lookup.insert(_equalityProxy);

    _equalityResolutionWithDeletion = OptionValue<RuleActivity>( "equality_resolution_with_deletion","erd");
    _equalityResolutionWithDeletion.description="";
    _equalityResolutionWithDeletion.setOptionValues(OptionValues("input_only","off","on"));
    _equalityResolutionWithDeletion.defaultValue=INPUT_ONLY;
    lookup.insert(OptionValues("input_only","off","on"));

  
    _extensionalityAllowPosEq = BoolOptionValue( "extensionality_allow_pos_eq","");
    _extensionalityAllowPosEq.description="";
    _extensionalityAllowPosEq.defaultValue=false;
    lookup.insert(_extensionalityAllowPosEq);

    _extensionalityMaxLength = UnsignedOptionValue("extensionality_max_length","");
    _extensionalityMaxLength.description="";
    _extensionalityMaxLength.defaultValue=0;
    lookup.insert(_extensionalityMaxLength);

    _extensionalityResolution = OptionValue<ExtensionalityResolution>("extensionality_resolution","er");
    _extensionalityResolution.description="";
    _extensionalityResolution.setOptionValues(OptionValues("filter","known","off"));
    _extensionalityResolution.defaultValue=OFF;
    lookup.insert(_extensionalityResolution);

    _flattenTopLevelConjunctions = BoolOptionValue("flatten_top_level_conjunctions","");
    _flattenTopLevelConjunctions.description=
             "split formulas with top-level (up to universal quantification) conjunctions into several formulas";
    _flattenTopLevelConjunctions.defaultValue=false;
    lookup.insert(_flattenTopLevelConjunctions);

    _forbiddenOptions_ = StringOptionValue("forbidden_options","");
    _forbiddenOptions_.description=
             "If some of the specified options are set to a forbidden state, vampire will fail to start, or in the CASC mode it will skip such strategies.";
    //_forbiddenOptions.defaultValue // no default
    lookup.insert(_forbiddenOptions);

    _forcedOptions = StringOptionValue("forced_options","");
    _forcedOptions.description=
             "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the option values set by other means (also inside CASC mode strategies)";
    //_forcedOptions.defaultValue // no default
    lookup.insert(_forcedOptions);
    
    _forwardDemodulation = OptionValue<Demodulation>("forward_demodulation","fd");
    _forwardDemodulation.description=
             "Oriented rewriting of newly derived clauses by kept unit equalities\n"
             "s = t     L[sθ] \\/ C\n"
             "---------------------  where sθ > tθ\n"
             " L[tθ] \\/ C\n"
             "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.";
    _forwardDemodulation.setOptionValues(OptionValues("all","off","preordered"));
    _forwardDemodulation.defaultValue=ALL;
    lookup.insert(_forwardDemodulation);

    _forwardLiteralRewriting = BoolOptionValue("forward_literal_rewriting","flr");
    _forwardLiteralRewriting.description="";
    _forwardLiteralRewriting.defaultValue=false;
    lookup.insert(_forwardLiteralRewriting);

    _forwardSubsumption = BoolOptionValue("forward_subsumption","fs");
    _forwardSubsumption.description="";
    _forwardSubsumption.defaultValue=true;
    lookup.insert(_forwardSubsumption);

    _forwardSubsumptionResolution = BoolOptionValue("forward_subsumption_resolution","fsr");
    _forwardSubsumptionResolution.description="";
    _forwardSubsumptionResolution.defaultValue=true;
    lookup.insert(_forwardSubsumptionResolution);

    _functionDefinitionElimination = OptionValue<FunctionDefinitionElimination>("function_definition_elimination","fde");
    _functionDefinitionElimination.description=
             "All literals of set-of-support clauses will be selected";
    _functionDefinitionElimination.setOptionValues(OptionValues("all","none","unused"));
    _functionDefinitionElimination.defaultValue=ALL;
    lookup.insert(_functionDefinitionElimination);

    _functionNumber = IntOptionValue("function_number","");
    _functionNumber.description="";
    _functionNumber.defaultValue=1;
    lookup.insert(_functionNumber);

    _generalSplitting = OptionValue("general_splitting","gsp");
    _generalSplitting.description=
             "Preprocessing rule that splits clauses in order to reduce number of different variables in each clause";
    _generalSplitting.setOptionValues(OptionValues("input_only","off","on"));
    _generalSplitting.defaultValue=OFF;
    lookup.insert(_generalSplitting);

    _globalSubsumption = BoolOptionValue("global_subsumption","gs");
    _globalSubsumption.description="";
    _globalSubsumption.defaultValue=false;
    lookup.insert(_globalSubsumption);

    _showHelp = BoolOptionValue("help","h");
    _showHelp.description="display this help";
    _showHelp.defaultValue=false;
    lookup.insert(_help);

    _hornRevealing= BoolOptionValue("horn_revealing","");
    _hornRevealing.description=
             "Preprocessing rule that tries to discover whether polarities of predicates can be changed, so that problem becomes horn. If successful, marks all clauses with a positive literal as axioms, and those with only negatives as conjectures.";
    _hornRevealing.defaultValue=false;
    lookup.insert(_hornRevealing);

    _hyperSuperposition = BoolOptionValue("hyper_superposition","");
    _hyperSuperposition.description=
             "Generating inference that attempts to do several rewritings at once if it will eliminate literals of the original clause (now we aim just for elimination by equality resolution)";
    _hyperSuperposition.defaultValue=false;
    lookup.insert(_hyperSuperposition);

    _ignoreMissing = BoolOptionValue("ignore_missing","");
    _ignoreMissing.description=
             "Ignore any options that have been removed (useful in CASC mode where this can cause errors)";
    _ignoreMissing.defaultValue=false;
    lookup.insert(_ignoreMissing);

    _include = OptionValue("include","");
    _include.description="Path prefix for the 'include' TPTP directive";
    _include.defaultValue="";
    lookup.insert(_include);

    _increasedNumeralWeight = BoolOptionValue("increased_numeral_weight","");
    _increasedNumeralWeight.description=
             "weight of integer constants depends on the logarithm of their absolute value (instead of being 1)";
    _increasedNumeralWeight.defaultValue=false;
    lookup.insert(_increasedNumeralWeight);

    _inequalitySplitting = IntOptionValue("inequality_splitting","ins");
    _inequalitySplitting.description="";
    _inequalitySplitting.defaultValue=3;
    lookup.insert(_inequalitySplitting);

    _inputFile= StringOptionValue("input_file","");
    _inputFile.description="Problem file to be solved (if not specified, standard input is used)";
    _inputFile.defaultValue="";
    lookup.insert();

    _inputSyntax= OptionValue<InputSyntax>("input_syntax","");
    _inputSyntax.description="";
    _inputSyntax.setOptionValues(OptionValues("simplify","smtlib","smtlib2","tptp";
                                              "xhuman","xmps","xnetlib"));
    _inputSyntax.defaultValue=
    //in case we compile vampire with bpa, then the default input syntax is smtlib
#if !GNUMP
    TPTP;
#else
    SMTLIB;
#endif
    lookup.insert(_inputSyntax);

    _instGenBigRestartRatio = fFloatOptionValue("inst_gen_big_restart_ratio","igbrr");
    _instGenBigRestartRatio.description=
             "determines how often a big restart (instance generation starts from input clauses) will be performed. Small restart means all clauses generated so far are processed again.";
    _instGenBigRestartRatiodefaultValue=0.0;
    lookup.insert(_instGenBigRestartRatio);

    _instGenInprocessing = BoolOptionValue("inst_gen_inprocessing","");
    _instGenInprocessing.description="";
    _instGenInprocessing.defaultValue=false;
    lookup.insert(_instGenInprocessing);

    _instGenPassiveReactivation = BoolOptionValue("inst_gen_passive_reactivation","");
    _instGenPassiveReactivation.description="";
    _instGenPassiveReactivation.defaultValue=false;
    lookup.insert(_instGenPassiveReactivation);

    _instGenResolutionInstGenRatio = RatioOptionValue("inst_gen_resolution_ratio","igrr");
    _instGenResolutionInstGenRatio.description=
             "ratio of resolution and instantiation steps (applies only if inst_gen_with_resolution is on)";
             false, "1/1"),
    _instGenResolutionInstGenRatio.defaultValue=1;
    _instGenResolutionInstGenRatio.defaultOtherValuse=1;
    lookup.insert(_instGenResolutionInstGenRatio);
    
    _instGenRestartPeriod = IntOptionValue("inst_gen_restart_period","igrp");
    _instGenRestartPeriod.description="how many clauses are processed before (small?) restart";
    _instGenRestartPeriod.defaultValue=1000;
    lookup.insert(_instGenRestartPeriod);

    _instGenRestartPeriodQuotient = FloatOptionValue("inst_gen_restart_period_quotient","igrpq");
    _instGenRestartPeriodQuotient.description="restart period is multiplied by this number after each restart";
    _instGenRestartPeriodQuotient.defaultValue=1.0;
    lookup.insert(_instGenRestartPeriodQuotient);

    _instGenSelection = IntOptionValue("inst_gen_selection","igs");
    _instGenSelection.description=
             "selection function for InstGen. we don't have the functions 11 and 1011 yet (as it would need special treatment for the look-ahead)";
    _instGenSelection.defaultValue=0;
    lookup.insert(_instGenSelection);

    _instGenWithResolution = BoolOptionValue("inst_gen_with_resolution","igwr");
    _instGenWithResolution.description=
             "performs instantiation together with resolution (global subsuption index is shared, also clauses generated by the resolution are added to the instance SAT problem)";
    _instGenWithResolutiondefaultValue=false;
    lookup.insert(_instGenWithResolution);

    _interpretedSimplification = BoolOptionValue("interpreted_simplification","");
    _interpretedSimplification.description=
             "Performs simplifications of interpreted functions. This option requires interpreted_evaluation to be enabled as well. IMPORTANT - Currently not supported";
    _interpretedSimplification.defaultValue=false;
    lookup.insert(_interpretedSimplification);

    _latexOutput = StringOptionValue("latex_output","");
    _latexOutput.description="File that will contain proof in the LaTeX format.";
    _.defaultValue="off";
    lookup.insert(_latexOutput);

    _lingvaAdditionalInvariants = StringOptionValue("lingva_additional_invariants","");
    _lingvaAdditionalInvariants.description="";
    _lingvaAdditionalInvariants.defaultValue="";
    lookup.insert(_lingvaAdditionalInvariants);

    _literalComparisonMode = OptionValue<LiteralComparisonMode>("literal_comparison_mode","lcm");
    _literalComparisonMode.description="";
    _literalComparisonMode.setOptionValues(OptionValues("predicate","reverse","standard"));
    _literalComparisonMode.defaultValue=STANDARD;
    lookup.insert(_literalComparisonMode);

    _logFile = StringOptionValue("log_file","");
    _logFile.description="";
    _logFile.defaultValue="off";
    lookup.insert(_logFile);

    _lrsFirstTimeCheck = IntOptionValue("lrs_first_time_check","");
    __lrsFirstTimeCheckdescription=
             "Percentage of time limit at which the LRS algorithm will for the first time estimate the number of reachable clauses.";
    _lrsFirstTimeCheck.defaultValue=5;
    lookup.insert(_lrsFirstTimeCheck);

    _lrsWeightLimitOnly = BoolOptionValue("lrs_weight_limit_only","");
    _lrsWeightLimitOnly.description=
             "If off, the lrs sets both age and weight limit according to clause reachability, otherwise it sets the age limit to 0 and only the weight limit reflects reachable clauses";
    _lrsWeightLimitOnly.defaultValue=false;
    lookup.insert(_lrsWeightLimitOnly);

    _maxActive = LongOptionValue("max_active","");
    _maxActive.description="";
    _maxActive.defaultValue=0;
    lookup.insert(_maxActive);

    _maxAnswers = IntOptionValue("max_answers","");
    _maxAnswers.description="";
    _maxAnswers.defaultValue=1;
    lookup.insert(_maxAnswers);

    _maxInferenceDepth = IntOptionValue("max_inference_depth","");
    _maxInferenceDepth.description="";
    _maxInferenceDepth.defaultValue=0;
    lookup.insert(_maxInferenceDepth);

    _maxPassive = LongOptionValue("max_passive","");
    _maxPassive.description="";
    _maxPassive.defaultValue=0;
    lookup.insert(_maxPassive);

    _maxWeight = IntOptionValue("max_weight","");
    _maxWeight.description="Weight limit for clauses (0 means no weight limit)";
    _maxWeight.defaultValue=0;
    lookup.insert(_maxWeight);

    _memoryLimit = OptionValue<size_t("memory_limit","m");
    _memoryLimit.description=
             "Memory limit in MB";
    _memoryLimit.defaultValue=
#if VDEBUG
             "1000";
#else
             "3000";
#endif
   lookup.insert(_memoryLimit);

    _mode = OptionValue<Mode>("mode","");
    _mode.description=
             "consequence_elimination mode forces values of unused_predicate_definition_removal and propositional_to_bdd to be off";
    _mode.setOptionValues(
                       OptionValues("axiom_selection","bpa","casc","casc_epr";
                                    "casc_ltb","casc_mzr","casc_sat","clausify";
                                    "consequence_elimination","grounding";
                                    "ltb_build","ltb_solve","output","preprocess";
                                    "profile","program_analysis","sat_solver";
                                    "spider","vampire"));
    _mode.defaultValue=VAMPIRE;
    lookup.insert(_mode);

    _namePrefix = StringOptionValue("name_prefix","");
    _namePrefix.description=
             "Prefix for symbols introduced by Vampire (BDD-related propositional predicates, naming predicates, Skolem functions)";
    _namePrefix.defaultValue="";
    lookup.insert(_namePrefix);

    _naming = IntOptionValue("naming","nm");
    _naming.description="";
    _naming.defaultValue=8;
    lookup.insert();

    _nicenessOption = OptionValue<NicenessOption>("niceness_option","no");
    _nicenessOption.description="";
    _nicenessOption.setOptionValues(OptionValues("average","none","sum","top"));
    _nicenessOption.defaultValue=NONE;
    lookup.insert(_nicenessOption);

    _nongoalWeightCoefficient = FloatOptionValue("nongoal_weight_coefficient","nwc");
    _nongoalWeightCoefficient.description=
             "coefficient that will multiply the weight of theory clauses (those marked as 'axiom' in TPTP)";
    _nongoalWeightCoefficient.defaultValue=1.0;
    lookup.insert(_nongoalWeightCoefficient);

    _nonliteralsInClauseWeight = BoolOptionValue("nonliterals_in_clause_weight","nicw");
    _nonliteralsInClauseWeight.description=
             "Non-literal parts of clauses (such as BDDs or its split history) will also contribute to the weight";
    _nonliteralsInClauseWeight.defaultValue=false;
    lookup.insert(_nonliteralsInClauseWeight);

    _normalize = BoolOptionValue("normalize","");
    _normalize.description="";
    _normalize.defaultValue=false;
    lookup.insert(_normalize);

    _outputAxiomNames = BoolOptionValue("output_axiom_names","");
    _outputAxiomNames.description="preserve names of axioms from the problem file in the proof output";
    _outputAxiomNames.defaultValue=false;
    lookup.insert(_outputAxiomNames);

    _predicateDefinitionInlining = OptionValue<InliningMode>("predicate_definition_inlining","");
    _predicateDefinitionInlining.description=
             "Determines whether predicate definitions should be inlined. Non_growing rules out inlinings that would lead to increase in the size of the problem";
    _predicateDefinitionInlining.setOptionValues(OptionValues("axioms_only","non_growwing","off","on"));
    _predicateDefinitionInlining.defaultValue=OFF;
    lookup.insert(_predicateDefinitionInlining);

    _predicateDefinitionMerging = BoolOptionValue("predicate_definition_merging","");
    _predicateDefinitionMerging.description=
             "Determines whetehr predicates with equivalent definitions will be merged into one. Look for pairs of definitions such as"
             "p(X) <=> F[X]"
             "q(X) <=> F[X]"
             "replace the latter by"
             "q(X) <=> p(X)"
             "and use it to eliminate the predicate q(X).";
    _predicateDefinitionMerging.defaultValue=false;
    lookup.insert(_predicateDefinitionMerging);

    _predicateEquivalenceDiscovery = OptionValue<PredicateEquivalenceDiscoveryMode>("predicate_equivalence_discovery","");
    _predicateEquivalenceDiscovery.description=
             "If enabled, SAT solver will be used to discover predicate equivalences during preprocessing. "
             "if all_atoms, equivalences between all atoms will be searched for. "
             "if definitions, we'll look only for equivalences in the shape of predicate definitions (this lies somewhere between on and all_atoms). "
             "if all_formulas, equivalences between all formulas are searched for";
    _predicateEquivalenceDiscovery.setOptionValues(OptionValues("all_atoms","all_formulas","definitions","off","on"));
    _predicateEquivalenceDiscovery.defaultValue=OFF;
    lookup.insert(_predicateEquivalenceDiscovery);

    _predicateEquivalenceDiscoveryAddImplications = BoolOptionValue("predicate_equivalence_discovery_add_implications","");
    _predicateEquivalenceDiscoveryAddImplications.description=
             "if predicate_equivalence_discovery is enabled, add also discoveder implications, not only equivalences";
    _predicateEquivalenceDiscoveryAddImplications.defaultValue=false;
    lookup.insert(_predicateEquivalenceDiscoveryAddImplications);

    _predicateEquivalenceDiscoveryRandomSimulation = BoolOptionValue("predicate_equivalence_discovery_random_simulation","");
    _predicateEquivalenceDiscoveryRandomSimulation.description=
             "use random simulation before the simultaneous sat-sweeping to reduce the amount of candidate equivalences";
    _predicateEquivalenceDiscoveryRandomSimulation.defaultValue=true;
    lookup.insert();

    _predicateEquivalenceDiscoverySatConflictLimit = IntOptionValue("predicate_equivalence_discovery_sat_conflict_limit","");
    _predicateEquivalenceDiscoverySatConflictLimit.description=
             "Limit on the number of SAT conflicts in each equivalence check. Default is -1 which stands for unlimited, 0 will restrict equivalence discovery to unit propagation. The implicative sat sweeping has an internal conflict count limit which always starts with zero and is increased geometrically until it reaches the limit set by this value";
    _predicateEquivalenceDiscoverySatConflictLimit.defaultValue=-1;
    lookup.insert(_predicateEquivalenceDiscoverySatConflictLimit);

    _predicateIndexIntroduction = BoolOptionValue("predicate_index_introduction","");
    _predicateIndexIntroduction.description=
             "If all atoms of a certain predicate contain distinct constants as a particular argument, atoms of the predicate"
             " are replaces by set of fresh predicates, one for each of the distinct constants.\n"
             "E.g. a problem\n"
             "p(a,b,X,1)\n"
             "p(a,c,a,2)\n"
             "will be transformed into\n"
             "p_a_1(b,X)\n"
             "p_a_2(c,a)\n"
             "(second argument is not removed because constants b and c are not necessarily distinct, and third argment is not replaced because it occurs as a variable)";
    _predicateIndexIntroduction.defaultValue=false;
    lookup.insert(_predicateIndexIntroduction);

    _printClausifierPremises = BoolOptionValue("print_clausifier_premises","");
    __printClausifierPremisesdescription="";
    _printClausifierPremises.defaultValue=false;
    lookup.insert(_printClausifierPremises);

    _problemName = OptionValue("problem_name","");
    _problemName.description="";
    _problemName.defaultValue="";
    lookup.insert(_problemName);

    _proof = OptionValue<Proof>("proof","p");
    _proof.description=
             "Specifies whether proof will be output. 'proofcheck' will output proof as a sequence of TPTP problems to allow for proof-checking.";
    _proof.setOptionValues(OptionValues("off","on","proofcheck","tptp"));
    _proof.defaultValue=ON;
    lookup.insert(_proof);

    _proofChecking = BoolOptionValue("proof_checking","");
    _proofChecking.description="";
    _proofChecking.defaultValue=false;
    lookup.insert(_proofChecking);

    _protectedPrefix = StringOptionValue("protected_prefix","");
    _protectedPrefix.description="Symbols with this prefix are immune against elimination during preprocessing";
    _protectedPrefix.defaultValue="";
    lookup.insert(_protectedPrefix);

    _questionAnswering = OptionValue<QuestionAnsweringMode>("question_answering","");
    _questionAnswering.description="Determines whether (and how) we attempt to answer questions";
    _questionAnswering.setOptionValues(OptionValues("answer_literal","from_proof","off"));
    _questionAnswering.defaultValue=OFF;
    lookup.insert(_questionAnswering);

    _randomSeed = IntOptionValue("random_seed","");
    _randomSeed.description="";
    _randomSeed.defaultValue=Random::seed();
    lookup.insert(_randomSeed);

    _rowVariableMaxLength = IntOptionValue("row_variable_max_length","");
    _rowVariableMaxLength.description="";
    _rowVariableMaxLength.defaultValue=2;
    lookup.insert(_rowVariableMaxLength);

    _satClauseActivityDecay = FloatOptionValue("sat_clause_activity_decay","");
    _satClauseActivityDecay.description="";
    _satClauseActivityDecay.defaultValue=1.00;
    lookup.insert(_satClauseActivityDecay);

    _satClauseDisposer = OptionValue<SatClauseDisposer>("sat_clause_disposer","");
    _satClauseDisposer.description="";
    _satClauseDisposer.setOptionValues(OptionValues("growing","minisat"));
    _satClauseDisposer.defaultValue=MINISAT;
    lookup.insert(_satClauseDisposer);

    _satLearntMinimization = BoolOptionValue("sat_learnt_minimization","");
    _satLearntMinimization.description="";
    _satLearntMinimization.defaultValue=true;
    lookup.insert(_satLearntMinimization);

    _satLearntSubsumptionResolution = BoolOptionValue("sat_learnt_subsumption_resolution","");
    _satLearntSubsumptionResolution.description="";
    _satLearntSubsumptionResolution.defaultValue=true;
    lookup.insert(_satLearntSubsumptionResolution);

    _satRestartFixedCount = IntOptionValue("sat_restart_fixed_count","");
    _satRestartFixedCount.description="";
    _satRestartFixedCount.defaultValue=16000;
    lookup.insert(_satRestartFixedCount);

    _satRestartGeometricIncrease = FloatOptionValue("sat_restart_geometric_increase","");
    _satRestartGeometricIncrease.description="";
    _satRestartGeometricIncrease.defaultValue=1.1;
    lookup.insert(_satRestartGeometricIncrease);

    _satRestartGeometricInit = IntOptionValue("sat_restart_geometric_init","");
    _satRestartGeometricInit.description="";
    _satRestartGeometricInit.defaultValue=32;
    lookup.insert(_satRestartGeometricInit);

    _satRestartLubyFactor = IntOptionValue("sat_restart_luby_factor","");
    _satRestartLubyFactor.description="";
    _satRestartLubyFactor.defaultValue=100;
    lookup.insert(_satRestartLubyFactor);

    _satRestartMinisatIncrease = FloatOptionValue("sat_restart_minisat_increase","");
    _satRestartMinisatIncrease.description="";
    _satRestartMinisatIncrease.defaultValue=1.1;
    lookup.insert(_satRestartMinisatIncrease);

    _satRestartMinisatInit = IntOptionValue("sat_restart_minisat_init","");
    _satRestartMinisatInit.description="";
    _satRestartMinisatInit.defaultValue=100;
    lookup.insert(_satRestartMinisatInit);

    _satRestartStrategy = OptionValue<SatRestartStrategy>("sat_restart_strategy","");
    _satRestartStrategy.description="";
    _satRestartStrategy.setOptionValues(OptionValues("fixed","geometric","luby","minisat"));
    _satRestartStrategy.defaultValue=LUBY;
    lookup.insert(_satRestartStrategy);

    _satSolver = OptionValue<SatSolver>("sat_solver","sas");
    _satSolver.description=
             "Select the SAT solver to be used throughout the solver. This will be used in AVATAR (for splitting) when the saturation algorithm is discount,lrs or otter and in instance generation for selection and global subsumption. The buf options are experimental (they add buffering).";
    _satSolver.setOptionValues(OptionValues("buf_lingeling","buf_vampire","lingeling","vampire"));
    _satSolver.defaultValue=VAMPIRE;
    lookup.insert(_satSolver);

    _satVarActivityDecay = FloatOptionValue("sat_var_activity_decay","");
    _satVarActivityDecay.description="";
    _satVarActivityDecay.defaultValue=1.05;
    lookup.insert(_satVarActivityDecay);

    _satVarSelector = OptionValueSatVarSelector>("sat_var_selector","svs");
    _satVarSelector.description="";
    _satVarSelector.setOptionValues(OptionValues("active","niceness","recently_learnt"));
    _satVarSelector.defaultValue=ACTIVE;
    lookup.insert(_satVarSelector);

    _saturationAlgorithm = OptionValue<SaturationAlgorithm>("saturation_algorithm","sa");
    _saturationAlgorithm.description=
             "inst_gen and tabulation aren't influenced by options for the saturation algorithm, apart from those mentioned. tabulation is a special goal-oriented mode for large theories. inst_gen is a simple implementation of instantiation calculus - global_subsumption, unit_resulting_resolution and age_weight_ratio are supported";
    _saturationAlgorithm.setOptionValues(OptionValues("discount","inst_gen","lrs","otter","tabulation"));
    _saturationAlgorithm.defaultValue=LRS;
    lookup.insert();

    _selection = IntOptionValue("selection","s");
    _selection.description="";
    _selection.defaultValue=10;
    lookup.insert(_selection);

    _showActive = BoolOptionValue("show_active","");
    _showActive.description="";
    _showActive.defaultValue=false;
    lookup.insert(_showActive);

    _showBlocked = BoolOptionValue("show_blocked","");
    _showBlocked.description="show generating inferences blocked due to coloring of symbols";
    _showBlocked.defaultValue=false;
    lookup.insert(_showBlocked);

    _showDefinitions = BoolOptionValue("show_definitions","");
    _showDefinitions.description="";
    _showDefinitions.defaultValue=false;
    lookup.insert(_showDefinitions);

    _showExperimentalOptions = BoolOptionValue("show_experimental_options","");
    _showExperimentalOptions.description="";
    _showExperimentalOptions.defaultValue=false;
    lookup.insert(_showExperimentalOptions);

    _showInterpolant = OptionValue<InterpolantMode>("show_interpolant","");
    _showInterpolant.description="minimized tries to find a nicer interpolant than the default algorithm does";
    _showInterpolant.setOptionValues(OptionValues("minimized","off","on"));
    _showInterpolant.defaultValue=OFF;
    lookup.insert(_showInterpolant);

    _showNew = BoolOptionValue("show_new","");
    _showNew.description="";
    _showNew.defaultValue=false;
    lookup.insert(_showNew);

    _showNewPropositional = BoolOptionValue("show_new_propositional","");
    _showNewPropositional.description="";
    _.defaultValue=false;
    lookup.insert(_showNewPropositional);

    _showNonconstantSkolemFunctionTrace = BoolOptionValue("show_nonconstant_skolem_function_trace","");
    _showNonconstantSkolemFunctionTrace.description="";
    _showNonconstantSkolemFunctionTrace.defaultValue=false;
    lookup.insert(_showNonconstantSkolemFunctionTrace);

    _showOptions = OptionValue<OptionTag>("show_options","");
    _showOptions.description="";
    _showOptions.setOptionValues(OptionValues("bp","off","on","vampire"));
    _showOptions.defaultValue=OFF;
    lookup.insert(_showOptions);

    _showPassive = BoolOptionValue("show_passive","");
    _showPassive.description="";
    _showPassive.defaultValue=false;
    lookup.insert(_showPassive);

    _showPreprocessing = BoolOptionValue("show_preprocessing","");
    _showPreprocessing.description="";
    _showPreprocessing.defaultValue=false;
    lookup.insert(_showPreprocessing);

    _showSkolemisations = BoolOptionValue("show_skolemisations","");
    _showSkolemisations.description="";
    _showSkolemisations.defaultValue=false;
    lookup.insert(_showSkolemisations);

    _showSymbolElimination = BoolOptionValue("show_symbol_elimination","");
    _showSymbolElimination.description="";
    _showSymbolElimination.defaultValue=false;
    lookup.insert(_showSymbolElimination);

    _showTheoryAxioms = BoolOptionValue("show_theory_axioms","");
    _showTheoryAxioms.description="";
    _showTheoryAxioms.defaultValue=false;
    lookup.insert(_showTheoryAxioms);

    _simulatedTimeLimit = IntOptionValue("simulated_time_limit","stl");
    _simulatedTimeLimit.description=
             "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)";
    _simulatedTimeLimit.defaultValue=0;
    lookup.insert(_simulatedTimeLimit);

    _sineDepth = UnsignedOptionValue("sine_depth","sd");
    _sineDepth.description=
             "Limit number of iterations of the transitive closure algorithm that selects formulas based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal limit (least selected axioms), 2 allows two iterations, etc...";
    _sineDepth.defaultValue=0;
    lookup.insert();

    _sineGeneralityThreshold = UnsignedOptionValue("sine_generality_threshold","sgt");
    _sineGeneralityThreshold.description=
             "Generality of a symbol is the number of input formulas in which a symbol appears. If the generality of a symbol is smaller than the threshold, it is always added into the D-relation with formulas in which it appears.";
    _sineGeneralityThreshold.defaultValue=0;
    lookup.insert();

    _sineSelection = OptionValue<SineSelection>("sine_selection","ss");
    _sineSelection.description=
             "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) are initially selected, and the SInE selection is performed on those annotated as 'axiom'. If 'included', all formulas that are directly in the problem file are initially selected, and the SInE selection is performed on formulas from included files. The 'included' value corresponds to the behaviour of the original SInE implementation.";
    _sineSelection.setOptionValues(OptionValues("axioms","included","off"));
    _sineSelection.defaultValue=OFF;
    lookup.insert(_sineSelection);

    _sineTolerance = FloatOptionValue("sine_tolerance","st");
    _sineTolerance.description="SInE tolerance parameter (sometimes referred to as 'benevolence')";
    _sineTolerance.defaultValue=1.0;
    lookup.insert(_sineTolerance);

    _smtlibConsiderIntsReal = BoolOptionValue("smtlib_consider_ints_real","");
    _smtlibConsiderIntsReal.description="all integers will be considered to be reals by the SMTLIB parser";
    _smtlibConsiderIntsReal.defaultValue=false;
    lookup.insert(_smtlibConsiderIntsReal);

    _smtlibFletAsDefinition = BoolOptionValue("smtlib_flet_as_definition","");
    _smtlibFletAsDefinition.description="";
    _smtlibFletAsDefinition.defaultValue=false;
    lookup.insert(_smtlibFletAsDefinition);

    _smtlibIntroduceAIGNames = BoolOptionValue("smtlib_introduce_aig_names","");
    _smtlibIntroduceAIGNames.description="";
    _smtlibIntroduceAIGNames.defaultValue=true;
    lookup.insert(_smtlibIntroduceAIGNames);

    _sos = OptionValue<Sos>("sos","sos");
    _sos.description=
             "Set of support strategy. All formulas annotated as theory axioms are put directly among active clauses, without performing any inferences between them. If all, select all literals of set-of-support clauses, ortherwise use the default literal selector.";
    _sos.setOptionValues(OptionValues("all","off","on"));
    _sos.defaultValue=OFF;
    lookup.insert(_sos);


    _splitting = BoolOptionValue("splitting","spl");
    _splitting.description="";
    _splitting.defaultValue=true;
    lookup.insert(_splitting);

    _ssplittingAddComplementary = OptionValue<SSplittingAddComplementary>("ssplitting_add_complementary","ssac");
    _ssplittingAddComplementary.description="";
    _ssplittingAddComplementary.setOptionValues(OptionValues("ground","none"));
    _ssplittingAddComplementary.defaultValue=GROUND;
    lookup.insert(_ssplittingAddComplementary);

    _ssplittingComponentSweeping = OptionValue<SSplittingComponentSweeping>("ssplitting_component_sweeping","");
    _ssplittingComponentSweeping.description=
             "The idea of component selection is described at the top of SSplitter.hpp. The meaning of options is: none .. no sweeping is done. only_new .. after each SAT model update we do sweeping on the newly selected components. all .. after each SAT model update we do sweeping on all selected components iterated .. like all except that we repeat the sweping while some components are being deselected";
    _ssplittingComponentSweeping.setOptionValues(OptionValues("all","iterated","none","only_new"));
    _ssplittingComponentSweeping.defaultValue=ITERATED;
    lookup.insert(_ssplittingComponentSweeping);

    _ssplittingCongruenceClosure = BoolOptionValue("ssplitting_congruence_closure","sscc");
    _ssplittingCongruenceClosure.description="";
    _ssplittingCongruenceClosure.defaultValue=false;
    lookup.insert(_ssplittingCongruenceClosure);

    _ssplittingEagerRemoval = BoolOptionValue("ssplitting_eager_removal","sser");
    _ssplittingEagerRemoval.description="";
    _ssplittingEagerRemoval.defaultValue=true;
    lookup.insert(_ssplittingEagerRemoval);

    _ssplittingFlushPeriod = UnsignedOptionValue("ssplitting_flush_period","ssfp");
    _ssplittingFlushPeriod.description=
             "after given number of generated clauses without deriving an empty clause, the splitting component selection is shuffled. If equal to zero, shuffling is never performed.";
    _ssplittingFlushPeriod.defaultValue=0;
    lookup.insert(_ssplittingFlushPeriod);

    _ssplittingFlushQuotient = FloatOptionValue("ssplitting_flush_quotient","ssfq");
    _ssplittingFlushQuotient.description=
             "after each flush, the ssplitting_flush_period is multiplied by the quotient";
    _ssplittingFlushQuotient.defaultValue=1.5;
    lookup.insert(_ssplittingFlushQuotient);

    _ssplittingNonsplittableComponents = OptionValue<SSplittingNonsplittableComponents>("ssplitting_nonsplittable_components","ssnc");
    _ssplittingNonsplittableComponents.description=
             "known .. SAT clauses will be learnt from non-splittable clauses that have corresponding components (if there is a component C with name SAT l, clause C | {l1,..ln} will give SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original FO clause C | {l1,..ln} and let the component selection update model, possibly adding the component clause C | {l}. all .. like known, except when we see a non-splittable clause that doesn't have a name, we introduce the name for it. all_dependent .. like all, but we don't introduce names for non-splittable clauses that don't depend on any components";
    _ssplittingNonsplittableComponents.setOptionValues(OptionValues("all","all_dependent","known","none"));
    _ssplittingNonsplittableComponents.defaultValue=KNOWN;
    lookup.insert(_ssplittingNonsplittableComponents);

    _statistics = OptionValue<Statistics>("statistics","");
    _statistics.description="";
    _statistics.setOptionValues(OptionValues("brief","full","none"));
    _statistics.defaultValue=FULL;
    lookup.insert(_statistics);

    _superpositionFromVariables = BoolOptionValue("superposition_from_variables","sfv");
    _superpositionFromVariables.description="";
    _superpositionFromVariables.defaultValue=true;
    lookup.insert(_superpositionFromVariables);

    _symbolPrecedence = OptionValue<SymbolPrecedence>("symbol_precedence","sp");
    _symbolPrecedence.description="";
    _symbolPrecedence.setOptionValues(OptionValues("arity","occurrence","reverse_arity"));
    _symbolPrecedence.defaultValue=ARITY;
    lookup.insert(_symbolPrecedence);

    _tabulationBwRuleSubsumptionResolutionByLemmas = BoolOptionValue("tabulation_bw_rule_subsumption_resolution_by_lemmas","tbsr");
    _tabulationBwRuleSubsumptionResolutionByLemmas.description="";
    _tabulationBwRuleSubsumptionResolutionByLemmas.defaultValue=true;
    lookup.insert(_tabulationBwRuleSubsumptionResolutionByLemmas);

    _tabulationFwRuleSubsumptionResolutionByLemmas = BoolOptionValue("tabulation_fw_rule_subsumption_resolution_by_lemmas","tfsr");
    _tabulationFwRuleSubsumptionResolutionByLemmas.description="";
    _tabulationFwRuleSubsumptionResolutionByLemmas.defaultValue=true;
    lookup.insert(_tabulationFwRuleSubsumptionResolutionByLemmas);

    _tabulationGoalAgeWeightRatio = RatioOptionValue("tabulation_goal_awr","tgawr");
    _tabulationGoalAgeWeightRatio.description=
             "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next goal clause to process";
    _tabulationGoalAgeWeightRatio.defaultValue=1;
    _tabulationGoalAgeWeightRatio.defaultOtherValue=1;
    lookup.insert(_tabulationGoalAgeWeightRatio);

    _tabulationGoaLemmalRatio = RatioOptionValue("tabulation_goal_lemma_ratio","tglr");
    _tabulationGoaLemmalRatio.description=
             "when saturation algorithm is set to tabulation, this option determines the ratio of processing new goals and lemmas";
    _tabulationGoaLemmalRatio.defaultValue=1;
    _tabulationGoaLemmalRatio.defaultOtherValue=1;
    lookup.insert(_tabulationGoaLemmalRatio);
    
    _tabulationInstantiateProducingRules = BoolOptionValue("tabulation_instantiate_producing_rules","tipr");
    _tabulationInstantiateProducingRules.description=
             "when saturation algorithm is set to tabulation, this option determines whether the producing rules will be made of theory clauses (in case it's off), or of their instances got from the substitution unifying them with the goal";
    _tabulationInstantiateProducingRules.defaultValue=true;
    lookup.insert(_tabulationInstantiateProducingRules);

    _tabulationLemmaAgeWeightRatio = RatioOptionValue("tabulation_lemma_awr","tlawr");
    _tabulationLemmaAgeWeightRatio.description=
             "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next lemma to process";
    _tabulationLemmaAgeWeightRatio.defaultValue=1;
    _tabulationLemmaAgeWeightRatio.defaultOtherValue=1;
    lookup.insert(_tabulationLemmaAgeWeightRatio);

    _testId = StringOptionValue("test_id","");
    _testId.description="";
    _testId.defaultValue="unspecified_test";
    lookup.insert();

    _thanks = StringOptionValue("thanks","");
    _thanks.description="";
    _thanks.defaultValue="Tanya";
    lookup.insert(_thanks);

    _theoryAxioms = BoolOptionValue("theory_axioms","");
    _theoryAxioms.description="";
    _.defaultValue=true;
    lookup.insert(_theoryAxioms);

    _timeLimitInDeciseconds = OptionValue("time_limit","t");
    _timeLimitInDeciseconds.description="Time limit in wall clock seconds";
    _timeLimitInDeciseconds.defaultValue=600;
    lookup.insert(_timeLimitInDeciseconds);

    _timeStatistics = BoolOptionValue("time_statistics","");
    _timeStatistics.description="Show how much running time was spent in each part of the Vampire";
    _timeStatistics.defaultValue=false;
    lookup.insert(_timeStatistics);

    _trivialPredicateRemoval = BoolOptionValue("trivial_predicate_removal","");
    _trivialPredicateRemoval.description= "remove predicates never occurring only positively or only negatively in a clause";
    _trivialPredicateRemoval.defaultValue=false;
    lookup.insert(_trivialPredicateRemoval);

    _unitResultingResolution = OptionValue<URResolution>("unit_resulting_resolution","urr");
    _unitResultingResolution.description=
             "uses unit resulting resolution only to derive empty clauses (may be useful for splitting)";
    _unitResultingResolution.setOptionValues(OptionValues("ec_only","off","on"));
    _unitResultingResolution.defaultValue=OFF;
    lookup.insert(_unitResultingResolution);

    _unusedPredicateDefinitionRemoval = BoolOptionValue("unused_predicate_definition_removal","updr");
    _unusedPredicateDefinitionRemoval.description="";
    _unusedPredicateDefinitionRemoval.defaultValue=true;
    lookup.insert(_unusedPredicateDefinitionRemoval);

    _use_dm = BoolOptionValue("use_dismatching","");
    _use_dm.description="";
    _use_dm.defaultValue=false;
    lookup.insert(_use_dm);

    _weightIncrement = BoolOptionValue("weight_increment","");
    _weightIncrement.description="";
    _weightIncrement.defaultValue=false;
    lookup.insert(_weightIncrement);

    _whileNumber = OptionValue("while_number","");
    _whileNumber.description="";
    _whileNumber.defaultValue=1;
    lookup.insert(_whileNumber);

    _xmlOutput = StringOptionValue("xml_output","");
    _xmlOutput.description="";
    _xmlOutput.defaultValue="off";
    lookup.insert(_xmlOutput);
    

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
    set(name,value,Constants::optionNames.findLong(name));
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
  CALL ("Options::set/2");
  set(name.c_str(),value.c_str());
} // Options::set/2

/**
 * Set option by its name, value, and index in the list of options.
 * If index is -1, then name does not correspond to any existing option.
 *
 * @since 13/11/2004 Manchester
 */
void Options::set(const char* name,const char* value, int index)
{
  CALL("Options::set/3");

    //onOffToBool(value,name)
    /*
     se BP_ALLOWED_FM_BALANCE: {
     if (Int::stringToUnsignedInt(value,unsignedValue)) {
     _bpAllowedFMBalance = unsignedValue;
     }
     else {
     USER_ERROR("The value must be an integer");
     }
    */


    USER_ERROR((string)"wrong value (" + value + ") for " + name);

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

  try {
    set(name,value,Constants::optionNames.findShort(name));
  }
  catch(ValueNotFoundException&) {
    // try to set it as a long name
    return set(name,value);
  }
} // Options::setShort

/**
 * Convert the string onOff to a boolean value. If onOff is not one
 * of "on" or "off", then raise a user error exception.
 * @since 15/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing for the splitting option
 * @since 31/07/2014 Manchester, allow true for on and false for off
 * @author Andrei Voronkov
 */
bool Options::onOffToBool (const char* onOff,const char* option)
{
  CALL("Options::onOffToBool");


  if (! strcmp(onOff,"on") || ! strcmp(onOff,"true")) {
    return true;
  }
  if (! strcmp(onOff,"off") || ! strcmp(onOff,"false")) {
    return false;
  }
  //TODO hopefully remove the need for this
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

  if(showOptions() != OFF_TAG){
    str << "=========== Options ==========\n";
    bool experimental = showExperimentalOptions();
    for (int i = 0;i < Constants::optionNames.length;i++) {
      Stack<OptionTag>::Iterator tags(Constants::optionNames[i].tags);
      while(tags.hasNext()){
        OptionTag this_tag = tags.next();
        if(showOptions() == GLOBAL_TAG || this_tag == GLOBAL_TAG || this_tag == showOptions()){
          if(experimental || !Constants::optionNames[i].experimental){
            str << Constants::optionNames[i] << endl;
          }
        }
      }
    }
    str << "======= End of options =======\n";
  }
  if(showHelp()){
    str << "=========== Usage ==========\n";
    str << "Call vampire using\n";
    str << "  vampire [options] [problem]\n";
    str << "For example,\n";
    str << "  vampire --mode casc --include ~/TPTP ~/TPTP/Problems/ALG/ALG150+1.p\n";

    str << "=========== Hints ==========\n";


    str << "=========== Options ==========\n";
    str << "To see a list of all options use\n  --show_options on\n";
    str << "To see a list of options for a particular mode use\n";
    str << "  --show_options <mode>\t(for example --show_options vampire)\n";
    //str << "By default experimental options will not be shown. To show ";
    //str << "these options use\n  --show_experimental_options on\n";
    str << "=========== End ==========\n";
  }


} // Options::output (ostream& str) const


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
//     XMLElement OptionValue("option",true);
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
  error: USER_ERROR("bad test id " + _testId);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == vstring::npos) { // not found
    goto error;
  }
  vstring timeString = testId.substr(index+1);
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
  vstring sel = testId.substr(0,index);
  Int::stringToInt(sel,selection);
  setSelection(selection);
  testId = testId.substr(index+1);

  if (testId == "") {
    goto error;
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

  cout << "generateTestId currently brokend" << endl; //TODO fix
  ASSERTION_VIOLATION;
/*
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
*/
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

  return _xmlOutput.value == "on" || _latexOutput.value == "on";
} // Output::outputSuppressed


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
void Options::checkGlobalOptionConstraints() const
{
  if (_aigDefinitionIntroductionThreshold.value==0) {
    USER_ERROR("aig_definition_introduction_threshold must be non-zero");
  }
  if (_equalityResolutionWithDeletion.value==RA_ON) {
    USER_ERROR("equality_resolution_with_deletion is not implemented for value \"on\"");
  }
  // 0 means infinity, so it is intentionally not if (unsignedValue < 2).
  if (_extensionalityMaxLength.value == 1) {
    USER_ERROR("extensionality clauses have to be at least of size 2");
  }
    
  if (_bfnt.value && !completeForNNE()) {
    USER_ERROR("The bfnt option can only be used with a strategy complete for non-Horn problems without equality");
  }
  if (_splitting.value && _saturationAlgorithm.value == INST_GEN) {
    USER_ERROR("saturation algorithm inst_gen cannot be used with sat splitting");
  }
  if (_extensionalityResolution.value != ER_OFF && _inequalitySplitting.value) {
    USER_ERROR("extensionality resolution can not be used together with inequality splitting");
  }
    if (_generalSplitting.value==RA_ON) {
        USER_ERROR("general_splitting is not implemented for value \"on\"");
    }
    if (_instGenBigRestartRatio.value<0.0f || _instGenBigRestartRatio.value>1.0f) {
        USER_ERROR("inst_gen_big_restart_ratio must be a number between 0 and 1 (inclusive)");
	}
	if (_instGenRestartPeriodQuotient.value<1.0f) {
        USER_ERROR("inst_gen_restart_period_quotient must be a number at least 1");
	}
	if (_satClauseActivityDecay.value<=1.0f) {
        USER_ERROR("sat_clause_activity_decay must be a number greater than 1");
	}
	if (_satRestartGeometricIncrease.value<=1.0f) {
        USER_ERROR("sat_restart_geometric_increase must be a number greater than 1");
	}
	if (_satRestartMinisatIncrease.value<=1.0f) {
        USER_ERROR("sat_restart_minisat_increase must be a number greater than 1");
	}
    if (_satVarActivityDecay.value<=1.0f) {
        USER_ERROR("sat_var_activity_decay must be a number greater than 1");
	}
	if (_sineTolerance.value!=0.0f && _sineTolerance.value<1.0f) {
        USER_ERROR("sine_tolerance value must be a float number greater than or equal to 1");
    }
    if (_ssplittingFlushQuotient.value<1.0f) {
        USER_ERROR("ssplitting_flush_quotient must greater than or equal to 1");
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
