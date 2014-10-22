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

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"
#include "Debug/Assertion.hpp"

#include "Lib/VString.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
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
 *
 * Options are divided by the mode they are applicable to. We then divid by tags where appropriate.
 * If an option is applicable to multiple modes but is not global it is put in the most obvious mode - usually Vampire.
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()

{
    CALL("Options::Options");
    
   // some options that were not give names previously
    _forceIncompleteness = BoolOptionValue("force_incompleteness","",false);
    _equivalentVariableRemoval = BoolOptionValue("equivalentVariableRemoval","",true);
    _bpCollapsingPropagation = BoolOptionValue("bp_collapsing_propagation","",false);
    _backjumpTargetIsDecisionPoint = BoolOptionValue("backjump_target_is_decision_point","",true);
    _selectUnusedVariablesFirst = BoolOptionValue("_selectUnusedVariablesFirst","",false);
    
//**********************************************************************
//*********************** GLOBAL, for all modes  ***********************
//**********************************************************************
    
    _memoryLimit = UnsignedOptionValue("memory_limit","m",
#if VDEBUG
                                       1000
#else
                                       3000
#endif
                                       );
    _memoryLimit.description="Memory limit in MB";
    _lookup.insert(&_memoryLimit);
    
    _mode = ChoiceOptionValue<Mode>("mode","",Mode::VAMPIRE,
                                    {"axiom_selection","bpa","casc","casc_epr",
                                        "casc_ltb","casc_mzr","casc_sat","clausify",
                                        "consequence_elimination","grounding",
                                        "ltb_build","ltb_solve","output","preprocess",
                                        "profile","program_analysis","sat_solver",
                                        "spider","vampire"});
    _mode.description=
    "consequence_elimination mode forces values of unused_predicate_definition_removal and propositional_to_bdd to be off";
    _lookup.insert(&_mode);
    
    _decode = StringOptionValue("decode","","");
    _decode.description="";
    _lookup.insert(&_decode);
    
    _forbiddenOptions = StringOptionValue("forbidden_options","","");
    _forbiddenOptions.description=
    "If some of the specified options are set to a forbidden state, vampire will fail to start, or in the CASC mode it will skip such strategies.";
    _lookup.insert(&_forbiddenOptions);
    
    _forcedOptions = StringOptionValue("forced_options","","");
    _forcedOptions.description=
    "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the option values set by other means (also inside CASC mode strategies)";
    _lookup.insert(&_forcedOptions);
    
    _showHelp = BoolOptionValue("help","h",false);
    _showHelp.description="display this help";
    _lookup.insert(&_showHelp);
    
    _showOptions = BoolOptionValue("show_options","",false);
    _showOptions.description="";
    _lookup.insert(&_showOptions);
    
    _showExperimentalOptions = BoolOptionValue("show_experimental_options","",false);
    _showExperimentalOptions.description="";
    _lookup.insert(&_showExperimentalOptions);
    _showExperimentalOptions.setExperimental(); // only we know about it!
    
    _ignoreMissing = BoolOptionValue("ignore_missing","",false);
    _ignoreMissing.description=
    "Ignore any options that have been removed (useful in CASC mode where this can cause errors)";
    _lookup.insert(&_ignoreMissing);
    
    _include = StringOptionValue("include","","");
    _include.description="Path prefix for the 'include' TPTP directive";
    _lookup.insert(&_include);
    
    _inputFile= InputFileOptionValue("input_file","","",this);
    _inputFile.description="Problem file to be solved (if not specified, standard input is used)";
    _lookup.insert(&_inputFile);
    
    _inputSyntax= ChoiceOptionValue<InputSyntax>("input_syntax","",
                                                 //in case we compile vampire with bpa, then the default input syntax is smtlib
#if !GNUMP
                                                 InputSyntax::TPTP,
#else
                                                 InputSyntax::SMTLIB,
#endif
                                                 {"simplify","smtlib","smtlib2","tptp","xhuman","xmps","xnetlib"});
    _inputSyntax.description="";
    _lookup.insert(&_inputSyntax);
    
    _namePrefix = StringOptionValue("name_prefix","","");
    _namePrefix.description=
    "Prefix for symbols introduced by Vampire (BDD-related propositional predicates, naming predicates, Skolem functions)";
    _lookup.insert(&_namePrefix);
    
    _problemName = StringOptionValue("problem_name","","");
    _problemName.description="";
    _lookup.insert(&_problemName);
    
    _proof = ChoiceOptionValue<Proof>("proof","p",Proof::ON,{"off","on","proofcheck","tptp"});
    _proof.description=
    "Specifies whether proof will be output. 'proofcheck' will output proof as a sequence of TPTP problems to allow for proof-checking.";
    _lookup.insert(&_proof);
    
    _proofChecking = BoolOptionValue("proof_checking","",false);
    _proofChecking.description="";
    _lookup.insert(&_proofChecking);
    _proofChecking.setExperimental(); // not sure it works!
    
    _protectedPrefix = StringOptionValue("protected_prefix","","");
    _protectedPrefix.description="Symbols with this prefix are immune against elimination during preprocessing";
    _lookup.insert(&_protectedPrefix);
    
    _statistics = ChoiceOptionValue<Statistics>("statistics","",Statistics::FULL,{"brief","full","none"});
    _statistics.description="";
    _lookup.insert(&_statistics);
    
    _testId = StringOptionValue("test_id","","unspecified_test");
    _testId.description="";
    _lookup.insert(&_testId);
    
    _thanks = StringOptionValue("thanks","","Tanya");
    _thanks.description="";
    _lookup.insert(&_thanks);
    
    _timeLimitInDeciseconds = TimeLimitOptionValue("time_limit","t",600);
    _timeLimitInDeciseconds.description="Time limit in wall clock seconds";
    _lookup.insert(&_timeLimitInDeciseconds);
    
    _timeStatistics = BoolOptionValue("time_statistics","",false);
    _timeStatistics.description="Show how much running time was spent in each part of the Vampire";
    _lookup.insert(&_timeStatistics);
    
//*********************** Preprocessing  ***********************
    

    
    _aigBddSweeping = BoolOptionValue("aig_bdd_sweeping","",false);
    _aigBddSweeping.description="For a description of these aig options see the paper 'Preprocessing Techniques for First-Order Clausification'. ";
    _lookup.insert(&_aigBddSweeping);
    _aigBddSweeping.tag(OptionTag::PREPROCESSING);
    
    _aigConditionalRewriting = BoolOptionValue("aig_conditional_rewriting","",false);
    _aigConditionalRewriting.description="";
    _lookup.insert(&_aigConditionalRewriting);
    _aigConditionalRewriting.tag(OptionTag::PREPROCESSING);
    
    _aigDefinitionIntroduction = BoolOptionValue("aig_definition_introduction","",false);
    _aigDefinitionIntroduction.description="";
    _lookup.insert(&_aigDefinitionIntroduction);
    _aigDefinitionIntroduction.tag(OptionTag::PREPROCESSING);
    
    _aigDefinitionIntroductionThreshold = UnsignedOptionValue("aig_definition_introduction_threshold","",4);
    _aigDefinitionIntroductionThreshold.description=
               "number of subformula occurrences needed to introduce a name for it (if aig_definition_introduction is enabled)";
    _lookup.insert(&_aigDefinitionIntroductionThreshold);
    _aigDefinitionIntroductionThreshold.tag(OptionTag::PREPROCESSING);
    _aigDefinitionIntroductionThreshold.addConstraint(new NotEqual<unsigned>(0));

    _aigFormulaSharing = BoolOptionValue("aig_formula_sharing","",false);
    _aigFormulaSharing.description="Detection and sharing of common subformulas using AIG representation";
    _lookup.insert(&_aigFormulaSharing);
    _aigFormulaSharing.tag(OptionTag::PREPROCESSING);
    
    _aigInliner = BoolOptionValue("aig_inliner","",false);
    _aigInliner.description="";
    _lookup.insert(&_aigInliner);
    _aigInliner.tag(OptionTag::PREPROCESSING);
    
    _arityCheck = BoolOptionValue("arity_check","",false);
    _arityCheck.description="The same symbol name cannot be used with multiple arities";
    _lookup.insert(&_arityCheck);
    _arityCheck.tag(OptionTag::PREPROCESSING);
    
    _distinctProcessor = BoolOptionValue("distinct_processor","",false);
    _distinctProcessor.description="handles $distinct predicates";
    _lookup.insert(&_distinctProcessor);
    _distinctProcessor.tag(OptionTag::PREPROCESSING);
    
    _eprPreservingNaming = BoolOptionValue("epr_preserving_naming","",false);
    _eprPreservingNaming.description=
    "Naming will not cause introduction of any non-constant functions."
    "The nonconstant functions can be introduced by naming in a name definition when a universal quantifier turns into an existential one and is skolemized.";
    _lookup.insert(&_eprPreservingNaming);
    _eprPreservingNaming.tag(OptionTag::PREPROCESSING);
    
    _eprPreservingSkolemization= BoolOptionValue("epr_preserving_skolemization","",false);
    _eprPreservingSkolemization.description="";
    _lookup.insert(&_eprPreservingSkolemization);
    _eprPreservingSkolemization.tag(OptionTag::PREPROCESSING);
    
    _eprRestoringInlining= BoolOptionValue("epr_restoring_inlining","",false);
    _eprRestoringInlining.description="";
    _lookup.insert(&_eprRestoringInlining);
    _eprRestoringInlining.tag(OptionTag::PREPROCESSING);
    
    _equalityPropagation = BoolOptionValue("equality_propagation","",false);
    _equalityPropagation.description=
    "propagate equalities in formulas, for example\n"
    "X=Y => X=f(Y) ---> X=f(X)\n"
    "Such propagation can simplify formulas early in the preprocessing and so help other preprocessing rules (namely dealing with predicate definitions).";
    _lookup.insert(&_equalityPropagation);
    _equalityPropagation.tag(OptionTag::PREPROCESSING);
    
    _flattenTopLevelConjunctions = BoolOptionValue("flatten_top_level_conjunctions","",false);
    _flattenTopLevelConjunctions.description=
    "split formulas with top-level (up to universal quantification) conjunctions into several formulas";
    _lookup.insert(&_flattenTopLevelConjunctions);
    _flattenTopLevelConjunctions.tag(OptionTag::PREPROCESSING);
    
    _functionDefinitionElimination = ChoiceOptionValue<FunctionDefinitionElimination>("function_definition_elimination","fde",
                                                                                      FunctionDefinitionElimination::ALL,{"all","none","unused"});
    _functionDefinitionElimination.description=
    "All literals of set-of-support clauses will be selected";
    _lookup.insert(&_functionDefinitionElimination);
    _functionDefinitionElimination.tag(OptionTag::PREPROCESSING);
    
    _functionNumber = IntOptionValue("function_number","",1);
    _functionNumber.description="";
    _lookup.insert(&_functionNumber);
    _functionNumber.tag(OptionTag::PREPROCESSING);
    
    _generalSplitting = ChoiceOptionValue<RuleActivity>("general_splitting","gsp",RuleActivity::OFF,{"input_only","off","on"});
    _generalSplitting.description=
    "Preprocessing rule that splits clauses in order to reduce number of different variables in each clause";
    _lookup.insert(&_generalSplitting);
    _generalSplitting.tag(OptionTag::PREPROCESSING);
    _generalSplitting.addConstraint(new NotEqual<RuleActivity>(RuleActivity::ON));
    
    _hornRevealing= BoolOptionValue("horn_revealing","",false);
    _hornRevealing.description=
    "Preprocessing rule that tries to discover whether polarities of predicates can be changed, so that problem becomes horn. If successful, marks all clauses with a positive literal as axioms, and those with only negatives as conjectures.";
    _lookup.insert(&_hornRevealing);
    _hornRevealing.tag(OptionTag::PREPROCESSING);
    
    _predicateDefinitionInlining = ChoiceOptionValue<InliningMode>("predicate_definition_inlining","",InliningMode::OFF,
                                                                   {"axioms_only","non_growwing","off","on"});
    _predicateDefinitionInlining.description=
    "Determines whether predicate definitions should be inlined. Non_growing rules out inlinings that would lead to increase in the size of the problem";
    _lookup.insert(&_predicateDefinitionInlining);
    _predicateDefinitionInlining.tag(OptionTag::PREPROCESSING);
    
    _predicateDefinitionMerging = BoolOptionValue("predicate_definition_merging","",false);
    _predicateDefinitionMerging.description=
    "Determines whether predicates with equivalent definitions will be merged into one. Look for pairs of definitions such as\n"
    "p(X) <=> F[X]\n"
    "q(X) <=> F[X]\n"
    "replace the latter by\n"
    "q(X) <=> p(X)\n"
    "and use it to eliminate the predicate q(X).";
    _lookup.insert(&_predicateDefinitionMerging);
    _predicateDefinitionMerging.tag(OptionTag::PREPROCESSING);
    
    _predicateEquivalenceDiscovery = ChoiceOptionValue<PredicateEquivalenceDiscoveryMode>("predicate_equivalence_discovery","",
                                                                                          PredicateEquivalenceDiscoveryMode::OFF,
                                                                                          {"all_atoms","all_formulas","definitions","off","on"});
    _predicateEquivalenceDiscovery.description=
    "If enabled, SAT solver will be used to discover predicate equivalences during preprocessing. "
    "if all_atoms, equivalences between all atoms will be searched for. "
    "if definitions, we'll look only for equivalences in the shape of predicate definitions (this lies somewhere between on and all_atoms). "
    "if all_formulas, equivalences between all formulas are searched for";
    _lookup.insert(&_predicateEquivalenceDiscovery);
    _predicateEquivalenceDiscovery.tag(OptionTag::PREPROCESSING);
    
    _predicateEquivalenceDiscoveryAddImplications = BoolOptionValue("predicate_equivalence_discovery_add_implications","",false);
    _predicateEquivalenceDiscoveryAddImplications.description=
    "if predicate_equivalence_discovery is enabled, add also discoveder implications, not only equivalences";
    _lookup.insert(&_predicateEquivalenceDiscoveryAddImplications);
    _predicateEquivalenceDiscoveryAddImplications.tag(OptionTag::PREPROCESSING);
    
    _predicateEquivalenceDiscoveryRandomSimulation = BoolOptionValue("predicate_equivalence_discovery_random_simulation","",true);
    _predicateEquivalenceDiscoveryRandomSimulation.description=
    "use random simulation before the simultaneous sat-sweeping to reduce the amount of candidate equivalences";
    _lookup.insert(&_predicateEquivalenceDiscoveryRandomSimulation);
    _predicateEquivalenceDiscoveryRandomSimulation.tag(OptionTag::PREPROCESSING);
    
    _predicateEquivalenceDiscoverySatConflictLimit = IntOptionValue("predicate_equivalence_discovery_sat_conflict_limit","",-1);
    _predicateEquivalenceDiscoverySatConflictLimit.description=
    "Limit on the number of SAT conflicts in each equivalence check. Default is -1 which stands for unlimited, 0 will restrict equivalence discovery to unit propagation. The implicative sat sweeping has an internal conflict count limit which always starts with zero and is increased geometrically until it reaches the limit set by this value";
    _lookup.insert(&_predicateEquivalenceDiscoverySatConflictLimit);
    _predicateEquivalenceDiscoverySatConflictLimit.tag(OptionTag::PREPROCESSING);
    
    _predicateIndexIntroduction = BoolOptionValue("predicate_index_introduction","",false);
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
    _lookup.insert(&_predicateIndexIntroduction);
    _predicateIndexIntroduction.tag(OptionTag::PREPROCESSING);

    _unusedPredicateDefinitionRemoval = BoolOptionValue("unused_predicate_definition_removal","updr",true);
    _unusedPredicateDefinitionRemoval.description="";
    _lookup.insert(&_unusedPredicateDefinitionRemoval);
    _unusedPredicateDefinitionRemoval.tag(OptionTag::PREPROCESSING);
    
    _trivialPredicateRemoval = BoolOptionValue("trivial_predicate_removal","",false);
    _trivialPredicateRemoval.description= "remove predicates never occurring only positively or only negatively in a clause";
    _lookup.insert(&_trivialPredicateRemoval);
    _trivialPredicateRemoval.tag(OptionTag::PREPROCESSING);
    
    _sineDepth = UnsignedOptionValue("sine_depth","sd",0);
    _sineDepth.description=
    "Limit number of iterations of the transitive closure algorithm that selects formulas based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal limit (least selected axioms), 2 allows two iterations, etc...";
    _lookup.insert(&_sineDepth);
    _sineDepth.tag(OptionTag::PREPROCESSING);
    
    _sineGeneralityThreshold = UnsignedOptionValue("sine_generality_threshold","sgt",0);
    _sineGeneralityThreshold.description=
    "Generality of a symbol is the number of input formulas in which a symbol appears. If the generality of a symbol is smaller than the threshold, it is always added into the D-relation with formulas in which it appears.";
    _lookup.insert(&_sineGeneralityThreshold);
    _sineGeneralityThreshold.tag(OptionTag::PREPROCESSING);
    
    _sineSelection = ChoiceOptionValue<SineSelection>("sine_selection","ss",SineSelection::OFF,{"axioms","included","off"});
    _sineSelection.description=
    "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) are initially selected, and the SInE selection is performed on those annotated as 'axiom'. If 'included', all formulas that are directly in the problem file are initially selected, and the SInE selection is performed on formulas from included files. The 'included' value corresponds to the behaviour of the original SInE implementation.";
    _lookup.insert(&_sineSelection);
    _sineSelection.tag(OptionTag::PREPROCESSING);
    
    _sineTolerance = FloatOptionValue("sine_tolerance","st",1.0);
    _sineTolerance.description="SInE tolerance parameter (sometimes referred to as 'benevolence')";
    _lookup.insert(&_sineTolerance);
    _sineTolerance.tag(OptionTag::PREPROCESSING);
    _sineTolerance.addConstraint(new Or<float>(new Equal<float>(0.0f),new GreaterThan<float>(1.0f,true) ));
    
    _naming = IntOptionValue("naming","nm",8);
    _naming.description="";
    _lookup.insert(&_naming);
    _naming.tag(OptionTag::PREPROCESSING);
    _naming.addConstraint(new LessThan<int>(32768));
    
    _rowVariableMaxLength = IntOptionValue("row_variable_max_length","",2);
    _rowVariableMaxLength.description="";
    _lookup.insert(&_rowVariableMaxLength);
    _rowVariableMaxLength.tag(OptionTag::PREPROCESSING);
    
//*********************** Output  ***********************
    
    // how is this used?
    _logFile = StringOptionValue("log_file","","off");
    _logFile.description="";
    _lookup.insert(&_logFile);
    _logFile.tag(OptionTag::OUTPUT);
    
    //used?
    _xmlOutput = StringOptionValue("xml_output","","off");
    _xmlOutput.description="";
    _lookup.insert(&_xmlOutput);
    _xmlOutput.tag(OptionTag::OUTPUT);
    
    //used?
    _latexOutput = StringOptionValue("latex_output","","off");
    _latexOutput.description="File that will contain proof in the LaTeX format.";
    _lookup.insert(&_latexOutput);
    _latexOutput.tag(OptionTag::OUTPUT);
    
    _outputAxiomNames = BoolOptionValue("output_axiom_names","",false);
    _outputAxiomNames.description="preserve names of axioms from the problem file in the proof output";
    _lookup.insert(&_outputAxiomNames);
    _outputAxiomNames.tag(OptionTag::OUTPUT);
    
    
    _printClausifierPremises = BoolOptionValue("print_clausifier_premises","",false);
    _printClausifierPremises.description="";
    _lookup.insert(&_printClausifierPremises);
    _printClausifierPremises.tag(OptionTag::OUTPUT);
    
    _showActive = BoolOptionValue("show_active","",false);
    _showActive.description="";
    _lookup.insert(&_showActive);
    _showActive.tag(OptionTag::OUTPUT);
    
    _showBlocked = BoolOptionValue("show_blocked","",false);
    _showBlocked.description="show generating inferences blocked due to coloring of symbols";
    _lookup.insert(&_showBlocked);
    _showBlocked.tag(OptionTag::OUTPUT);
    
    _showDefinitions = BoolOptionValue("show_definitions","",false);
    _showDefinitions.description="";
    _lookup.insert(&_showDefinitions);
    _showDefinitions.tag(OptionTag::OUTPUT);
    
    
    _showNew = BoolOptionValue("show_new","",false);
    _showNew.description="";
    _lookup.insert(&_showNew);
    _showNew.tag(OptionTag::OUTPUT);
    
    _showNewPropositional = BoolOptionValue("show_new_propositional","",false);
    _showNewPropositional.description="";
    _lookup.insert(&_showNewPropositional);
    _showNewPropositional.tag(OptionTag::OUTPUT);
    
    _showNonconstantSkolemFunctionTrace = BoolOptionValue("show_nonconstant_skolem_function_trace","",false);
    _showNonconstantSkolemFunctionTrace.description="";
    _lookup.insert(&_showNonconstantSkolemFunctionTrace);
    _showNonconstantSkolemFunctionTrace.tag(OptionTag::OUTPUT);
    
    
    _showPassive = BoolOptionValue("show_passive","",false);
    _showPassive.description="";
    _lookup.insert(&_showPassive);
    _showPassive.tag(OptionTag::OUTPUT);
    
    _showPreprocessing = BoolOptionValue("show_preprocessing","",false);
    _showPreprocessing.description="";
    _lookup.insert(&_showPreprocessing);
    _showPreprocessing.tag(OptionTag::OUTPUT);
    
    _showSkolemisations = BoolOptionValue("show_skolemisations","",false);
    _showSkolemisations.description="";
    _lookup.insert(&_showSkolemisations);
    _showSkolemisations.tag(OptionTag::OUTPUT);
    
    _showSymbolElimination = BoolOptionValue("show_symbol_elimination","",false);
    _showSymbolElimination.description="";
    _lookup.insert(&_showSymbolElimination);
    _showSymbolElimination.tag(OptionTag::OUTPUT);
    
    _showTheoryAxioms = BoolOptionValue("show_theory_axioms","",false);
    _showTheoryAxioms.description="";
    _lookup.insert(&_showTheoryAxioms);
    _showTheoryAxioms.tag(OptionTag::OUTPUT);
    
//************************************************************************
//*********************** VAMPIRE (includes CASC)  ***********************
//************************************************************************
    
//*********************** Saturation  ***********************    
    
    _saturationAlgorithm = ChoiceOptionValue<SaturationAlgorithm>("saturation_algorithm","sa",SaturationAlgorithm::LRS,
                                                                  {"discount","inst_gen","lrs","otter","tabulation"});
    _saturationAlgorithm.description=
    "Select the saturation algorithm:\n"
    " - discount:\n"
    " - otter:\n"
    " - limited resource:\n"
    " - instance generation: a simple implementation of instantiation calculus\n    (global_subsumption, unit_resulting_resolution and age_weight_ratio)\n"
    " - tabulation: a special goal-oriented mode for large theories.\n"
    "inst_gen and tabulation aren't influenced by options for the saturation algorithm, apart from those under the relevant heading";
    _lookup.insert(&_saturationAlgorithm);
    _saturationAlgorithm.tag(OptionTag::SATURATION);
    _saturationAlgorithm.addConstraint(new Dependence<SaturationAlgorithm,bool>(
      new equals<SaturationAlgorithm>(SaturationAlgorithm::INST_GEN),&_splitting,new notequals<bool>(true)));
    
    _selection = SelectionOptionValue("selection","s",10);
    _selection.description=
    "Selection methods 2,3,4,10,11 are complete by virtue of extending Maximal i.e. they select the best among maximal. Methods 1002,1003,1004,1010,1011 relax this restriction and are therefore not complete.\n"
    " 0     - Total (select everything)\n"
    " 1     - Maximal\n"
    " 2     - ColoredFirst, MaximalSize then Lexigraphical\n"
    " 3     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,\n          LeastDistinctVariables then Lexigraphical\n"
    " 4     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,\n          LeastVariables, MaximalSize then Lexigraphical\n"
    " 10    - ColoredFirst, NegativeEquality, MaximalSize, Negative then Lexigraphical\n"
    " 11    - Lookahead\n"
    " 1002  - Incomplete version of 2\n"
    " 1003  - Incomplete version of 3\n"
    " 1004  - Incomplete version of 4\n"
    " 1010  - Incomplete version of 10\n"
    " 1011  - Incomplete version of 11\n"
    "Or negated, which means that reversePolarity is true (?)\n";
    
    _lookup.insert(&_selection);
    _selection.tag(OptionTag::SATURATION);
    
    _ageWeightRatio = RatioOptionValue("age_weight_ratio","awr",1,1);
    _ageWeightRatio.description=
    "Ratio in which clauses are being selected for activation i.e. a:w means that for every a clauses selected based on age"
    "there will be w selected based on weight.";
    _lookup.insert(&_ageWeightRatio);
    _ageWeightRatio.tag(OptionTag::SATURATION);
    
    _lrsFirstTimeCheck = IntOptionValue("lrs_first_time_check","",0);
    _lrsFirstTimeCheck.description=
    "Percentage of time limit at which the LRS algorithm will for the first time estimate the number of reachable clauses.";
    _lookup.insert(&_lrsFirstTimeCheck);
    _lrsFirstTimeCheck.tag(OptionTag::SATURATION);
    _lrsFirstTimeCheck.addConstraint(new GreaterThan<int>(0,true));
    _lrsFirstTimeCheck.addConstraint(new LessThan<int>(100));
    
    _lrsWeightLimitOnly = BoolOptionValue("lrs_weight_limit_only","",false);
    _lrsWeightLimitOnly.description=
    "If off, the lrs sets both age and weight limit according to clause reachability, otherwise it sets the age limit to 0 and only the weight limit reflects reachable clauses";
    _lookup.insert(&_lrsWeightLimitOnly);
    _lrsWeightLimitOnly.tag(OptionTag::SATURATION);
    
    _simulatedTimeLimit = TimeLimitOptionValue("simulated_time_limit","stl",0);
    _simulatedTimeLimit.description=
    "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)";
    _lookup.insert(&_simulatedTimeLimit);
    _simulatedTimeLimit.tag(OptionTag::SATURATION);
    
    _sos = ChoiceOptionValue<Sos>("sos","sos",Sos::OFF,{"all","off","on"});
    _sos.description=
    "Set of support strategy. All formulas annotated as theory axioms are put directly among active clauses, without performing any inferences between them. If all, select all literals of set-of-support clauses, ortherwise use the default literal selector.";
    _lookup.insert(&_sos);
    _sos.tag(OptionTag::SATURATION);
    
//*********************** Inferences  ***********************
    
    _backwardDemodulation = ChoiceOptionValue<Demodulation>("backward_demodulation","bd",
                                                            Demodulation::ALL,
                                                            {"all","off","preordered"});
    _backwardDemodulation.description=
             "Oriented rewriting of kept clauses by newly derived unit equalities\n"
             "s = t     L[sθ] \\/ C\n"
             "---------------------   where sθ > tθ (replaces RHS)\n"
             " L[tθ] \\/ C\n";
    _lookup.insert(&_backwardDemodulation);
    _backwardDemodulation.tag(OptionTag::INFERENCES);
    
    _backwardSubsumption = ChoiceOptionValue<Subsumption>("backward_subsumption","",
                                                          Subsumption::ON,{"off","on","unit_only"});
    _backwardSubsumption.description=
             "unit_only means that the subsumption will be performed only by unit clauses";
    _lookup.insert(&_backwardSubsumption);
    _backwardSubsumption.tag(OptionTag::INFERENCES);
    
    _backwardSubsumptionResolution = ChoiceOptionValue<Subsumption>("backward_subsumption_resolution","bsr",
                                                                    Subsumption::OFF,{"off","on","unit_only"});
    _backwardSubsumptionResolution.description=
             "unit_only means that the subsumption resolution will be performed only by unit clauses";
    _lookup.insert(&_backwardSubsumptionResolution);
    _backwardSubsumptionResolution.tag(OptionTag::INFERENCES);
    
    _binaryResolution = BoolOptionValue("binary_resolution","br",true);
    _binaryResolution.description=
          "Standard binary resolution i.e.\n"
              "C \\/ t     D \\/ s\n"
              "---------------------\n"
              "(C \\/ D)θ\n"
              "where θ = mgu(t,-s) and t selected";
    _lookup.insert(&_binaryResolution);
    _binaryResolution.tag(OptionTag::INFERENCES);

    _condensation = ChoiceOptionValue<Condensation>("condensation","cond",Condensation::OFF,{"fast","off","on"});
    _condensation.description=
             "If 'fast' is specified, we only perform condensations that are easy to check for.";
    _lookup.insert(&_condensation);
    _condensation.tag(OptionTag::INFERENCES);

    _demodulationRedundancyCheck = BoolOptionValue("demodulation_redundancy_check","drc",true);
    _demodulationRedundancyCheck.description=
             "Avoids the following cases of backward and forward demodulation, as they do not preserve completeness:\n"
             "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n"

             "--------------------- \t ---------------------\n" 
             "t = t1 \\/ C \t\t t != t1 \\/ C\n"
             "where t > t1 and s = t > C (RHS replaced)";
    _lookup.insert(&_demodulationRedundancyCheck);
    _demodulationRedundancyCheck.tag(OptionTag::INFERENCES);

    // preprocessing?
    _equalityProxy = ChoiceOptionValue<EqualityProxy>( "equality_proxy","ep",EqualityProxy::OFF,{"R","RS","RST","RSTC","off"});
    _equalityProxy.description="";
    _lookup.insert(&_equalityProxy);
    
    _equalityResolutionWithDeletion = ChoiceOptionValue<RuleActivity>( "equality_resolution_with_deletion","erd",
                                                                      RuleActivity::INPUT_ONLY,{"input_only","off","on"});
    _equalityResolutionWithDeletion.description="";
    _lookup.insert(&_equalityResolutionWithDeletion);
    _equalityResolutionWithDeletion.tag(OptionTag::INFERENCES);
    _equalityResolutionWithDeletion.addConstraint(new NotEqual<RuleActivity>(RuleActivity::ON));
    
    
    _extensionalityAllowPosEq = BoolOptionValue( "extensionality_allow_pos_eq","",false);
    _extensionalityAllowPosEq.description="";
    _lookup.insert(&_extensionalityAllowPosEq);
    _extensionalityAllowPosEq.tag(OptionTag::INFERENCES);
    
    _extensionalityMaxLength = UnsignedOptionValue("extensionality_max_length","",0);
    _extensionalityMaxLength.description="";
    _lookup.insert(&_extensionalityMaxLength);
    _extensionalityMaxLength.tag(OptionTag::INFERENCES);
    // 0 means infinity, so it is intentionally not if (unsignedValue < 2).
    _extensionalityMaxLength.addConstraint(new NotEqual<unsigned>(1));
    
    _extensionalityResolution = ChoiceOptionValue<ExtensionalityResolution>("extensionality_resolution","er",
                                                                            ExtensionalityResolution::OFF,{"filter","known","off"});
    _extensionalityResolution.description="";
    _lookup.insert(&_extensionalityResolution);
    _extensionalityResolution.tag(OptionTag::INFERENCES);
    _extensionalityResolution.addConstraint(new Dependence<ExtensionalityResolution,int>(
      new notequals<ExtensionalityResolution>(ExtensionalityResolution::OFF),&_inequalitySplitting,new equals<int>(0)));
    
    _forwardDemodulation = ChoiceOptionValue<Demodulation>("forward_demodulation","fd",Demodulation::ALL,{"all","off","preordered"});
    _forwardDemodulation.description=
    "Oriented rewriting of newly derived clauses by kept unit equalities\n"
    "s = t     L[sθ] \\/ C\n"
    "---------------------  where sθ > tθ\n"
    " L[tθ] \\/ C\n"
    "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.";
    _lookup.insert(&_forwardDemodulation);
    _forwardDemodulation.tag(OptionTag::INFERENCES);
    
    _forwardLiteralRewriting = BoolOptionValue("forward_literal_rewriting","flr",false);
    _forwardLiteralRewriting.description="";
    _lookup.insert(&_forwardLiteralRewriting);
    _forwardLiteralRewriting.tag(OptionTag::INFERENCES);
    
    _forwardSubsumption = BoolOptionValue("forward_subsumption","fs",true);
    _forwardSubsumption.description="";
    _lookup.insert(&_forwardSubsumption);
    _forwardSubsumption.tag(OptionTag::INFERENCES);
    
    _forwardSubsumptionResolution = BoolOptionValue("forward_subsumption_resolution","fsr",true);
    _forwardSubsumptionResolution.description="";
    _lookup.insert(&_forwardSubsumptionResolution);
    _forwardSubsumptionResolution.tag(OptionTag::INFERENCES);
    
    _hyperSuperposition = BoolOptionValue("hyper_superposition","",false);
    _hyperSuperposition.description=
    "Generating inference that attempts to do several rewritings at once if it will eliminate literals of the original clause (now we aim just for elimination by equality resolution)";
    _lookup.insert(&_hyperSuperposition);
    _hyperSuperposition.tag(OptionTag::INFERENCES);
    
    _unitResultingResolution = ChoiceOptionValue<URResolution>("unit_resulting_resolution","urr",URResolution::OFF,{"ec_only","off","on"});
    _unitResultingResolution.description=
    "uses unit resulting resolution only to derive empty clauses (may be useful for splitting)";
    _lookup.insert(&_unitResultingResolution);
    _unitResultingResolution.tag(OptionTag::INFERENCES);
    
    _superpositionFromVariables = BoolOptionValue("superposition_from_variables","sfv",true);
    _superpositionFromVariables.description="";
    _lookup.insert(&_superpositionFromVariables);
    _superpositionFromVariables.tag(OptionTag::INFERENCES);
    
//*********************** InstGen  ***********************

    _globalSubsumption = BoolOptionValue("global_subsumption","gs",false);
    _globalSubsumption.description="";
    _lookup.insert(&_globalSubsumption);
    _globalSubsumption.tag(OptionTag::INST_GEN);
    
    _instGenBigRestartRatio = FloatOptionValue("inst_gen_big_restart_ratio","igbrr",0.0);
    _instGenBigRestartRatio.description=
    "determines how often a big restart (instance generation starts from input clauses) will be performed. Small restart means all clauses generated so far are processed again.";
    _lookup.insert(&_instGenBigRestartRatio);
    _instGenBigRestartRatio.tag(OptionTag::INST_GEN);
    _instGenBigRestartRatio.addConstraint(new GreaterThan<float>(0.0f,true));
    _instGenBigRestartRatio.addConstraint(new LessThan<float>(1.0f,true));
    
    _instGenInprocessing = BoolOptionValue("inst_gen_inprocessing","",false);
    _instGenInprocessing.description="";
    _lookup.insert(&_instGenInprocessing);
    _instGenInprocessing.tag(OptionTag::INST_GEN);
    
    _instGenPassiveReactivation = BoolOptionValue("inst_gen_passive_reactivation","",false);
    _instGenPassiveReactivation.description="";
    _lookup.insert(&_instGenPassiveReactivation);
    _instGenPassiveReactivation.tag(OptionTag::INST_GEN);
    
    _instGenResolutionInstGenRatio = RatioOptionValue("inst_gen_resolution_ratio","igrr",1,1);
    _instGenResolutionInstGenRatio.description=
    "ratio of resolution and instantiation steps (applies only if inst_gen_with_resolution is on)";
    _lookup.insert(&_instGenResolutionInstGenRatio);
    _instGenResolutionInstGenRatio.tag(OptionTag::INST_GEN);
    
    _instGenRestartPeriod = IntOptionValue("inst_gen_restart_period","igrp",1000);
    _instGenRestartPeriod.description="how many clauses are processed before (small?) restart";
    _lookup.insert(&_instGenRestartPeriod);
    _instGenRestartPeriod.tag(OptionTag::INST_GEN);
    
    _instGenRestartPeriodQuotient = FloatOptionValue("inst_gen_restart_period_quotient","igrpq",1.0);
    _instGenRestartPeriodQuotient.description="restart period is multiplied by this number after each restart";
    _lookup.insert(&_instGenRestartPeriodQuotient);
    _instGenRestartPeriodQuotient.tag(OptionTag::INST_GEN);
    _instGenRestartPeriodQuotient.addConstraint(new GreaterThan<float>(1.0f,true));
    
    _instGenSelection = SelectionOptionValue("inst_gen_selection","igs",0);
    _instGenSelection.description=
    "selection function for InstGen. we don't have the functions 11 and 1011 yet (as it would need special treatment for the look-ahead)";
    _lookup.insert(&_instGenSelection);
    _instGenSelection.tag(OptionTag::INST_GEN);
    
    _instGenWithResolution = BoolOptionValue("inst_gen_with_resolution","igwr",false);
    _instGenWithResolution.description=
    "performs instantiation together with resolution (global subsuption index is shared, also clauses generated by the resolution are added to the instance SAT problem)";
    _lookup.insert(&_instGenWithResolution);
    _instGenWithResolution.tag(OptionTag::INST_GEN);
    
    _use_dm = BoolOptionValue("use_dismatching","",false);
    _use_dm.description="";
    _lookup.insert(&_use_dm);
    _use_dm.tag(OptionTag::INST_GEN);
    _use_dm.setExperimental();
    
    _nicenessOption = ChoiceOptionValue<Niceness>("niceness_option","no",Niceness::NONE,{"average","none","sum","top"});
    _nicenessOption.description="";
    _lookup.insert(&_nicenessOption);
    _nicenessOption.tag(OptionTag::INST_GEN);
    _nicenessOption.setExperimental();
    
//*********************** AVATAR  ***********************
    
    _splitting = BoolOptionValue("splitting","spl",true);
    _splitting.description="";
    _lookup.insert(&_splitting);
    _splitting.tag(OptionTag::AVATAR);
    
    _ssplittingAddComplementary = ChoiceOptionValue<SSplittingAddComplementary>("ssplitting_add_complementary","ssac",
                                                                                SSplittingAddComplementary::GROUND,{"ground","none"});
    _ssplittingAddComplementary.description="";
    _lookup.insert(&_ssplittingAddComplementary);
    _ssplittingAddComplementary.tag(OptionTag::AVATAR);
    _ssplittingAddComplementary.setExperimental();
    
    _ssplittingComponentSweeping = ChoiceOptionValue<SSplittingComponentSweeping>("ssplitting_component_sweeping","",
                                                                                  SSplittingComponentSweeping::ITERATED,
                                                                                  {"all","iterated","none","only_new"});
    _ssplittingComponentSweeping.description=
    "The idea of component selection is described at the top of SSplitter.hpp. The meaning of options is: none .. no sweeping is done. only_new .. after each SAT model update we do sweeping on the newly selected components. all .. after each SAT model update we do sweeping on all selected components iterated .. like all except that we repeat the sweping while some components are being deselected";
    _lookup.insert(&_ssplittingComponentSweeping);
    _ssplittingComponentSweeping.tag(OptionTag::AVATAR);
    _ssplittingComponentSweeping.setExperimental();
    
    _ssplittingCongruenceClosure = BoolOptionValue("ssplitting_congruence_closure","sscc",false);
    _ssplittingCongruenceClosure.description="";
    _lookup.insert(&_ssplittingCongruenceClosure);
    _ssplittingCongruenceClosure.tag(OptionTag::AVATAR);
    
    _ssplittingEagerRemoval = BoolOptionValue("ssplitting_eager_removal","sser",true);
    _ssplittingEagerRemoval.description="";
    _lookup.insert(&_ssplittingEagerRemoval);
    _ssplittingEagerRemoval.tag(OptionTag::AVATAR);
    _ssplittingEagerRemoval.setExperimental();
    
    _ssplittingFlushPeriod = UnsignedOptionValue("ssplitting_flush_period","ssfp",0);
    _ssplittingFlushPeriod.description=
    "after given number of generated clauses without deriving an empty clause, the splitting component selection is shuffled. If equal to zero, shuffling is never performed.";
    _lookup.insert(&_ssplittingFlushPeriod);
    _ssplittingFlushPeriod.tag(OptionTag::AVATAR);
    _ssplittingFlushPeriod.setExperimental();
    
    _ssplittingFlushQuotient = FloatOptionValue("ssplitting_flush_quotient","ssfq",1.5);
    _ssplittingFlushQuotient.description=
    "after each flush, the ssplitting_flush_period is multiplied by the quotient";
    _lookup.insert(&_ssplittingFlushQuotient);
    _ssplittingFlushQuotient.tag(OptionTag::AVATAR);
    _ssplittingFlushQuotient.setExperimental();
    _ssplittingFlushQuotient.addConstraint(new GreaterThan<float>(1.0f,true));
    
    _ssplittingNonsplittableComponents = ChoiceOptionValue<SSplittingNonsplittableComponents>("ssplitting_nonsplittable_components","ssnc",
                                                                                              SSplittingNonsplittableComponents::KNOWN,
                                                                                              {"all","all_dependent","known","none"});
    _ssplittingNonsplittableComponents.description=
    "known .. SAT clauses will be learnt from non-splittable clauses that have corresponding components (if there is a component C with name SAT l, clause C | {l1,..ln} will give SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original FO clause C | {l1,..ln} and let the component selection update model, possibly adding the component clause C | {l}. all .. like known, except when we see a non-splittable clause that doesn't have a name, we introduce the name for it. all_dependent .. like all, but we don't introduce names for non-splittable clauses that don't depend on any components";
    _lookup.insert(&_ssplittingNonsplittableComponents);
    _ssplittingNonsplittableComponents.tag(OptionTag::AVATAR);
    _ssplittingNonsplittableComponents.setExperimental();

    
//*********************** SAT solver (used in various places)  ***********************
    
    _satClauseActivityDecay = FloatOptionValue("sat_clause_activity_decay","",1.001f);
    _satClauseActivityDecay.description="";
    _lookup.insert(&_satClauseActivityDecay);
    _satClauseActivityDecay.tag(OptionTag::SAT);
    _satClauseActivityDecay.addConstraint(new GreaterThan<float>(1.0f));
    
    _satClauseDisposer = ChoiceOptionValue<SatClauseDisposer>("sat_clause_disposer","",SatClauseDisposer::MINISAT,
                                                              {"growing","minisat"});
    _satClauseDisposer.description="";
    _lookup.insert(&_satClauseDisposer);
    _satClauseDisposer.tag(OptionTag::SAT);
    
    _satLearntMinimization = BoolOptionValue("sat_learnt_minimization","",true);
    _satLearntMinimization.description="";
    _lookup.insert(&_satLearntMinimization);
    _satLearntMinimization.tag(OptionTag::SAT);
    
    _satLearntSubsumptionResolution = BoolOptionValue("sat_learnt_subsumption_resolution","",true);
    _satLearntSubsumptionResolution.description="";
    _lookup.insert(&_satLearntSubsumptionResolution);
    _satLearntSubsumptionResolution.tag(OptionTag::SAT);
    
    _satRestartFixedCount = IntOptionValue("sat_restart_fixed_count","",16000);
    _satRestartFixedCount.description="";
    _lookup.insert(&_satRestartFixedCount);
    _satRestartFixedCount.tag(OptionTag::SAT);
    
    _satRestartGeometricIncrease = FloatOptionValue("sat_restart_geometric_increase","",1.1);
    _satRestartGeometricIncrease.description="";
    _lookup.insert(&_satRestartGeometricIncrease);
    _satRestartGeometricIncrease.tag(OptionTag::SAT);
    _satRestartGeometricIncrease.addConstraint(new GreaterThan<float>(1.0f));
    
    _satRestartGeometricInit = IntOptionValue("sat_restart_geometric_init","",32);
    _satRestartGeometricInit.description="";
    _lookup.insert(&_satRestartGeometricInit);
    _satRestartGeometricInit.tag(OptionTag::SAT);
    
    _satRestartLubyFactor = IntOptionValue("sat_restart_luby_factor","",100);
    _satRestartLubyFactor.description="";
    _lookup.insert(&_satRestartLubyFactor);
    _satRestartLubyFactor.tag(OptionTag::SAT);
    
    _satRestartMinisatIncrease = FloatOptionValue("sat_restart_minisat_increase","",1.1);
    _satRestartMinisatIncrease.description="";
    _lookup.insert(&_satRestartMinisatIncrease);
    _satRestartMinisatIncrease.tag(OptionTag::SAT);
    _satRestartMinisatIncrease.addConstraint(new GreaterThan<float>(1.0f));
    
    _satRestartMinisatInit = IntOptionValue("sat_restart_minisat_init","",100);
    _satRestartMinisatInit.description="";
    _lookup.insert(&_satRestartMinisatInit);
    _satRestartMinisatInit.tag(OptionTag::SAT);
    
    _satRestartStrategy = ChoiceOptionValue<SatRestartStrategy>("sat_restart_strategy","",SatRestartStrategy::LUBY,
                                                                {"fixed","geometric","luby","minisat"});
    _satRestartStrategy.description="";
    _lookup.insert(&_satRestartStrategy);
    _satRestartStrategy.tag(OptionTag::SAT);
    
    _satSolver = ChoiceOptionValue<SatSolver>("sat_solver","sas",SatSolver::VAMPIRE,
                                              {"buf_lingeling","buf_minisat","buf_vampire","lingeling","minisat","vampire"});
    _satSolver.description=
    "Select the SAT solver to be used throughout the solver. This will be used in AVATAR (for splitting) when the saturation algorithm is discount,lrs or otter and in instance generation for selection and global subsumption. The buf options are experimental (they add buffering).";
    _lookup.insert(&_satSolver);
    _satSolver.tag(OptionTag::SAT);
    
    _satVarActivityDecay = FloatOptionValue("sat_var_activity_decay","",1.05f);
    _satVarActivityDecay.description="";
    _lookup.insert(&_satVarActivityDecay);
    _satVarActivityDecay.tag(OptionTag::SAT);
    _satVarActivityDecay.addConstraint(new GreaterThan<float>(1.0f));
    
    _satVarSelector = ChoiceOptionValue<SatVarSelector>("sat_var_selector","svs",SatVarSelector::ACTIVE,
                                                        {"active","niceness","recently_learnt"});
    _satVarSelector.description="";
    _lookup.insert(&_satVarSelector);
    _satVarSelector.tag(OptionTag::SAT);
    
    _satLingelingSimilarModels = BoolOptionValue("sat_lingeling_similar_models","",false);
    _satLingelingSimilarModels.description="";
    _lookup.insert(&_satLingelingSimilarModels);
    _satLingelingSimilarModels.tag(OptionTag::SAT);
    _satLingelingSimilarModels.setExperimental();

    _satLingelingIncremental = BoolOptionValue("sat_lingeling_incremental","",false);
    _satLingelingIncremental.description="";
    _lookup.insert(&_satLingelingIncremental);
    _satLingelingIncremental.tag(OptionTag::SAT);
    _satLingelingIncremental.setExperimental();

 //*********************** Tabulation  ***********************
    
    _tabulationBwRuleSubsumptionResolutionByLemmas = BoolOptionValue("tabulation_bw_rule_subsumption_resolution_by_lemmas","tbsr",true);
    _tabulationBwRuleSubsumptionResolutionByLemmas.description="";
    _lookup.insert(&_tabulationBwRuleSubsumptionResolutionByLemmas);
    _tabulationBwRuleSubsumptionResolutionByLemmas.tag(OptionTag::TABULATION);
    
    _tabulationFwRuleSubsumptionResolutionByLemmas = BoolOptionValue("tabulation_fw_rule_subsumption_resolution_by_lemmas","tfsr",true);
    _tabulationFwRuleSubsumptionResolutionByLemmas.description="";
    _lookup.insert(&_tabulationFwRuleSubsumptionResolutionByLemmas);
    _tabulationFwRuleSubsumptionResolutionByLemmas.tag(OptionTag::TABULATION);
    
    _tabulationGoalAgeWeightRatio = RatioOptionValue("tabulation_goal_awr","tgawr",1,1);
    _tabulationGoalAgeWeightRatio.description=
    "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next goal clause to process";
    _lookup.insert(&_tabulationGoalAgeWeightRatio);
    _tabulationGoalAgeWeightRatio.tag(OptionTag::TABULATION);
    
    _tabulationGoalLemmaRatio = RatioOptionValue("tabulation_goal_lemma_ratio","tglr",1,1);
    _tabulationGoalLemmaRatio.description=
    "when saturation algorithm is set to tabulation, this option determines the ratio of processing new goals and lemmas";
    _lookup.insert(&_tabulationGoalLemmaRatio);
    _tabulationGoalLemmaRatio.tag(OptionTag::TABULATION);
    
    _tabulationInstantiateProducingRules = BoolOptionValue("tabulation_instantiate_producing_rules","tipr",true);
    _tabulationInstantiateProducingRules.description=
    "when saturation algorithm is set to tabulation, this option determines whether the producing rules will be made of theory clauses (in case it's off), or of their instances got from the substitution unifying them with the goal";
    _lookup.insert(&_tabulationInstantiateProducingRules);
    _tabulationInstantiateProducingRules.tag(OptionTag::TABULATION);
    
    _tabulationLemmaAgeWeightRatio = RatioOptionValue("tabulation_lemma_awr","tlawr",1,1);
    _tabulationLemmaAgeWeightRatio.description=
    "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next lemma to process";
    _lookup.insert(&_tabulationLemmaAgeWeightRatio);
    _tabulationLemmaAgeWeightRatio.tag(OptionTag::TABULATION);
    
    //*************************************************************
    //*********************** which mode or tag?  ************************
    //*************************************************************
    
    _bfnt = BoolOptionValue("bfnt","bfnt",false);
    _bfnt.description="";
    _lookup.insert(&_bfnt);
    _bfnt.tag(OptionTag::OTHER);
    _bfnt.addConstraint(new OnAnd(new RequiresCompleteForNonHorn<bool>()));
    
    _increasedNumeralWeight = BoolOptionValue("increased_numeral_weight","",false);
    _increasedNumeralWeight.description=
             "weight of integer constants depends on the logarithm of their absolute value (instead of being 1)";
    _lookup.insert(&_increasedNumeralWeight);
    _increasedNumeralWeight.tag(OptionTag::OTHER);

    _inequalitySplitting = IntOptionValue("inequality_splitting","ins",3);
    _inequalitySplitting.description="";
    _lookup.insert(&_inequalitySplitting);
    _inequalitySplitting.tag(OptionTag::OTHER);

    _interpretedSimplification = BoolOptionValue("interpreted_simplification","",false);
    _interpretedSimplification.description=
             "Performs simplifications of interpreted functions. This option requires interpreted_evaluation to be enabled as well. IMPORTANT - Currently not supported";
    _lookup.insert(&_interpretedSimplification);
    _interpretedSimplification.tag(OptionTag::OTHER);


    _literalComparisonMode = ChoiceOptionValue<LiteralComparisonMode>("literal_comparison_mode","lcm",
                                                                      LiteralComparisonMode::STANDARD,
                                                                      {"predicate","reverse","standard"});
    _literalComparisonMode.description="";
    _lookup.insert(&_literalComparisonMode);
    _literalComparisonMode.tag(OptionTag::OTHER);


    _maxActive = LongOptionValue("max_active","",0);
    _maxActive.description="";
    _lookup.insert(&_maxActive);
    _maxActive.tag(OptionTag::OTHER);

    _maxAnswers = IntOptionValue("max_answers","",1);
    _maxAnswers.description="";
    _lookup.insert(&_maxAnswers);
    _maxAnswers.tag(OptionTag::OTHER);

    _maxInferenceDepth = IntOptionValue("max_inference_depth","",0);
    _maxInferenceDepth.description="";
    _lookup.insert(&_maxInferenceDepth);
    _maxInferenceDepth.tag(OptionTag::OTHER);

    _maxPassive = LongOptionValue("max_passive","",0);
    _maxPassive.description="";
    _lookup.insert(&_maxPassive);
    _maxPassive.tag(OptionTag::OTHER);

    _maxWeight = IntOptionValue("max_weight","",0);
    _maxWeight.description="Weight limit for clauses (0 means no weight limit)";
    _lookup.insert(&_maxWeight);
    _maxWeight.tag(OptionTag::OTHER);

    _nonGoalWeightCoefficient = NonGoalWeightOptionValue("nongoal_weight_coefficient","nwc",1.0);
    _nonGoalWeightCoefficient.description=
             "coefficient that will multiply the weight of theory clauses (those marked as 'axiom' in TPTP)";
    _lookup.insert(&_nonGoalWeightCoefficient);
    _nonGoalWeightCoefficient.tag(OptionTag::OTHER);

    _nonliteralsInClauseWeight = BoolOptionValue("nonliterals_in_clause_weight","nicw",false);
    _nonliteralsInClauseWeight.description=
             "Non-literal parts of clauses (such as BDDs or its split history) will also contribute to the weight";
    _lookup.insert(&_nonliteralsInClauseWeight);
    _nonliteralsInClauseWeight.tag(OptionTag::OTHER);

    _normalize = BoolOptionValue("normalize","",false);
    _normalize.description="";
    _lookup.insert(&_normalize);
    _normalize.tag(OptionTag::OTHER);

    _questionAnswering = ChoiceOptionValue<QuestionAnsweringMode>("question_answering","",QuestionAnsweringMode::OFF,
                                                                  {"answer_literal","from_proof","off"});
    _questionAnswering.description="Determines whether (and how) we attempt to answer questions";
    _lookup.insert(&_questionAnswering);
    _questionAnswering.tag(OptionTag::OTHER);

    _randomSeed = IntOptionValue("random_seed","",Random::seed());
    _randomSeed.description="";
    _lookup.insert(&_randomSeed);
    _randomSeed.tag(OptionTag::OTHER);




    _symbolPrecedence = ChoiceOptionValue<SymbolPrecedence>("symbol_precedence","sp",SymbolPrecedence::ARITY,
                                                            {"arity","occurrence","reverse_arity"});
    _symbolPrecedence.description="";
    _lookup.insert(&_symbolPrecedence);



    _theoryAxioms = BoolOptionValue("theory_axioms","",true);
    _theoryAxioms.description="";
    _lookup.insert(&_theoryAxioms);





    _weightIncrement = BoolOptionValue("weight_increment","",false);
    _weightIncrement.description="";
    _lookup.insert(&_weightIncrement);

    _whileNumber = IntOptionValue("while_number","",1);
    _whileNumber.description="";
    _lookup.insert(&_whileNumber);


    //******************************************************************
    //*********************** Vinter???  *******************************
    //******************************************************************

    
    _colorUnblocking = BoolOptionValue("color_unblocking","",false);
    _colorUnblocking.description="";
    _lookup.insert(&_colorUnblocking);
    _colorUnblocking.setExperimental();
    
    _smtlibConsiderIntsReal = BoolOptionValue("smtlib_consider_ints_real","",false);
    _smtlibConsiderIntsReal.description="all integers will be considered to be reals by the SMTLIB parser";
    _lookup.insert(&_smtlibConsiderIntsReal);
    _smtlibConsiderIntsReal.setExperimental();
    
    _smtlibFletAsDefinition = BoolOptionValue("smtlib_flet_as_definition","",false);
    _smtlibFletAsDefinition.description="";
    _lookup.insert(&_smtlibFletAsDefinition);
    _smtlibFletAsDefinition.setExperimental();
    
    _smtlibIntroduceAIGNames = BoolOptionValue("smtlib_introduce_aig_names","",true);
    _smtlibIntroduceAIGNames.description="";
    _lookup.insert(&_smtlibIntroduceAIGNames);
    _smtlibIntroduceAIGNames.setExperimental();
    
    _showInterpolant = ChoiceOptionValue<InterpolantMode>("show_interpolant","",InterpolantMode::OFF,
                                                          {"minimized","off","on"});
    _showInterpolant.description="minimized tries to find a nicer interpolant than the default algorithm does";
    _lookup.insert(&_showInterpolant);
    _showInterpolant.tag(OptionTag::OUTPUT);
    _showInterpolant.setExperimental();
    
//******************************************************************
//*********************** Program Analysis  ************************
//******************************************************************
    
    _lingvaAdditionalInvariants = StringOptionValue("lingva_additional_invariants","","");
    _lingvaAdditionalInvariants.description="";
    _lookup.insert(&_lingvaAdditionalInvariants);
    _lingvaAdditionalInvariants.tag(Mode::PROGRAM_ANALYSIS);
    
//******************************************************************
//*********************** Bound Propagation  ***********************
//******************************************************************
    
    _bpCollapsingPropagation = BoolOptionValue("bp_add_collapsing_inequalities","",false); // ASSUMED default, wasn't in Options
    _bpCollapsingPropagation.description="";
    _lookup.insert(&_bpCollapsingPropagation);
    _bpCollapsingPropagation.tag(Mode::BOUND_PROP);
    
    _bpAllowedFMBalance = UnsignedOptionValue("bp_allowed_fm_balance","",0);
    _bpAllowedFMBalance.description="";
    _lookup.insert(&_bpAllowedFMBalance);
    _bpAllowedFMBalance.tag(Mode::BOUND_PROP);
    
    _bpAlmostHalfBoundingRemoval= ChoiceOptionValue<BPAlmostHalfBoundingRemoval>("bp_almost_half_bounding_removal","",
                                                                                 BPAlmostHalfBoundingRemoval::ON,{"bounds_on","off","on"});
    _bpAlmostHalfBoundingRemoval.description="";
    _lookup.insert(&_bpAlmostHalfBoundingRemoval);
    _bpAlmostHalfBoundingRemoval.tag(Mode::BOUND_PROP);
    
    _bpAssignmentSelector = ChoiceOptionValue<BPAssignmentSelector>("bp_assignment_selector","",
                                                                    BPAssignmentSelector::RANDOM,
                                                                    {"alternating","bmp","lower_bound",
                                                                        "middle","random","rational","smallest",
                                                                        "tight","tightish","upper_bound"});
    _bpAssignmentSelector.description="";
    _lookup.insert(&_bpAssignmentSelector);
    _bpAssignmentSelector.tag(Mode::BOUND_PROP);
    
    _updatesByOneConstraint= UnsignedOptionValue("bp_bound_improvement_limit","",3);
    _updatesByOneConstraint.description="";
    _lookup.insert(&_updatesByOneConstraint);
    _updatesByOneConstraint.tag(Mode::BOUND_PROP);
    
    _bpConflictSelector = ChoiceOptionValue<BPConflictSelector>("bp_conflict_selector","",
                                                                BPConflictSelector::MOST_RECENT,{"least_recent","most_recent","shortest"});
    _bpConflictSelector.description="";
    _lookup.insert(&_bpConflictSelector);
    _bpConflictSelector.tag(Mode::BOUND_PROP);
    
    _bpConservativeAssignmentSelection = BoolOptionValue("bp_conservative_assignment_selection","",true);
    _bpConservativeAssignmentSelection.description="";
    _lookup.insert(&_bpConservativeAssignmentSelection);
    _bpConservativeAssignmentSelection.tag(Mode::BOUND_PROP);
    
    _bpFmElimination= BoolOptionValue("bp_fm_elimination","",true);
    _bpFmElimination.description="";
    _lookup.insert(&_bpFmElimination);
    _bpFmElimination.tag(Mode::BOUND_PROP);
    
    _maximalPropagatedEqualityLength = UnsignedOptionValue("bp_max_prop_length","",5);
    _maximalPropagatedEqualityLength.description="";
    _lookup.insert(&_maximalPropagatedEqualityLength);
    _maximalPropagatedEqualityLength.tag(Mode::BOUND_PROP);
    
    _bpPropagateAfterConflict = BoolOptionValue("bp_propagate_after_conflict","",true);
    _bpPropagateAfterConflict.description="";
    _lookup.insert(&_bpPropagateAfterConflict);
    _bpPropagateAfterConflict.tag(Mode::BOUND_PROP);
    
    _bpStartWithPrecise = BoolOptionValue("bp_start_with_precise","",false);
    _bpStartWithPrecise.description="";
    _lookup.insert(&_bpStartWithPrecise);
    _bpStartWithPrecise.tag(Mode::BOUND_PROP);
    
    _bpStartWithRational = BoolOptionValue("bp_start_with_rational","",false);
    _bpStartWithRational.description="";
    _lookup.insert(&_bpStartWithRational);
    _bpStartWithRational.tag(Mode::BOUND_PROP);
    
    _bpVariableSelector = ChoiceOptionValue<BPVariableSelector>("bp_variable_selector","",
                                                                BPVariableSelector::TIGHTEST_BOUND,
                                                                {"conflicting","conflicting_and_collapsing",
                                                                    "first","look_ahead","random","recent_collapsing",
                                                                    "recent_conflicting","tightest_bound"});
    _bpVariableSelector.description="";
    _lookup.insert(&_bpVariableSelector);
    _bpVariableSelector.tag(Mode::BOUND_PROP);
 
    
 // Declare tag names
    
    _tagNames = {
                 "Other",
                 "Output",
                 "Tabulation",
                 "Instance Generation", 
                 "SAT Solving",
                 "AVATAR",
                 "Inferences",
                 "Saturation",
                 "Preprocessing",
                 "Global"
                };

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
    if(!_lookup.findLong(name)->set(value)){
      USER_ERROR((vstring) value +" is an invalid value for "+(vstring)name+", see help");
    }
  }
  catch (const ValueNotFoundException&) {
    if (!_ignoreMissing.actualValue) {
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
    if(!_lookup.findShort(name)->set(value)){
      USER_ERROR((vstring) value +" is an invalid value for "+(vstring)name+", see help");
    }
  }
  catch (const ValueNotFoundException&) {
    if (!_ignoreMissing.actualValue) {
      USER_ERROR((vstring)name + " is not a valid option as a short option");
    }
  }
} // Options::setShort


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

  if(showHelp()){
    str << "=========== Usage ==========\n";
    str << "Call vampire using\n";
    str << "  vampire [options] [problem]\n";
    str << "For example,\n";
    str << "  vampire --mode casc --include ~/TPTP ~/TPTP/Problems/ALG/ALG150+1.p\n";

    str << "=========== Hints ==========\n";


    str << "=========== Options ==========\n";
    str << "To see a list of all options use\n  --show_options on\n";
    str << "Options will only be displayed for the current mode (Vampire by default)\n";
    str << " use --mode to change mode\n";
    //str << "By default experimental options will not be shown. To show ";
    //str << "these options use\n  --show_experimental_options on\n";
    str << "=========== End ==========\n";
  }

  if(showOptions()){

    //We bypass the allocator here because of the use of vstringstream
    BYPASSING_ALLOCATOR;

    Mode this_mode = _mode.actualValue;
    str << "=========== Options ==========\n";
    bool experimental = showExperimentalOptions();

    VirtualIterator<AbstractOptionValue*> options = _lookup.values();

    Stack<vstringstream*> groups;
    int num_tags = static_cast<int>(OptionTag::LAST_TAG);
    for(int i=0; i<=num_tags;i++){
      groups.push(new vstringstream);
    }

    while(options.hasNext()){
      AbstractOptionValue* option = options.next();
      if(option->inMode(this_mode) && (experimental || !option->experimental)){
        unsigned tag = static_cast<unsigned>(option->getTag());
        option->output(*groups[tag]);
      }
    }

    //output them in reverse order
    for(int i=num_tags;i>=0;i--){
      vstring label = "  "+_tagNames[i]+"  ";
      ASS(label.length() < 40);
      vstring br = "******************************";
      vstring br_gap = br.substr(0,(br.length()-(label.length()/2)));
      str << endl << br << br << endl;
      str << br_gap << label << br_gap << endl;
      str << br << br << endl << endl;
      str << (*groups[i]).str();
      BYPASSING_ALLOCATOR;
      delete groups[i];
    }

    str << "======= End of options =======\n";
  }

} // Options::output (ostream& str) const


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
void Options::RatioOptionValue::readRatio(const char* val, char separator)
{
  CALL("RatioOptionValue::readRatio");

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
    actualValue = age;
    int weight;
    if (! Int::stringToInt(copy+colonIndex+1,weight)) {
      USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
    }
    otherValue = weight;
    return;
  }
  actualValue = 1;
  int weight;
  if (! Int::stringToInt(val,weight)) {
    USER_ERROR((vstring)"wrong value for age-weight ratio: " + val);
  }
  otherValue = weight;
}

bool Options::NonGoalWeightOptionValue::set(const vstring& value)
{
  CALL("NonGoalWeightOptionValue::set");

 float newValue;
 if(!Int::stringToFloat(value.c_str(),newValue)) return false;

 if(newValue <= 0.0) return false;

 actualValue=newValue;

  // actualValue contains numerator
  numerator=static_cast<int>(newValue*100);
  // otherValue contains denominator
  denominator=100;

  return true;


}

bool Options::SelectionOptionValue::set(const vstring& value)
{
  CALL("SelectionOptionValue::set");

  int sel;
  if(!Int::stringToInt(value,sel)) return false;
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
    actualValue = sel;
    return true;
  default:
    return false;
  }
}

bool Options::InputFileOptionValue::set(const vstring& value)
{
  CALL("InputFileOptionValue::set");

  actualValue=value;
  if(value.empty()) return true;

  //update the problem name

  int length = value.length() - 1;
  const char* name = value.c_str();

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

  parent->_problemName.actualValue=value.substr(b,e-b);

  return true;

}


bool Options::TimeLimitOptionValue::set(const vstring& value)
{
  CALL("Options::readTimeLimit");

  int length = value.size();
  if (length == 0 || length > 127) {
    USER_ERROR((vstring)"wrong value for time limit: " + value);
  }

  char copy[128];
  strcpy(copy,value.c_str());
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
    USER_ERROR((vstring)"wrong value for time limit: " + value);
  }

#ifdef _MSC_VER
  // Visual C++ does not know the round function
  actualValue= (int)floor(number * multiplier);
#else
  actualValue= (int)round(number * multiplier);
#endif

  actualValue = actualValue/10; //TODO check that this is correct wrt old code

  return true;
} // Options::readTimeLimit(const char* val)


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

  _normalize.actualValue = true;
  _testId.actualValue = testId;

  vstring ma(testId,0,3); // the first 3 characters
  if (ma == "dis") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::DISCOUNT;
  }
  else if (ma == "lrs") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::LRS;
  }
  else if (ma == "ott") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::OTTER;
  }
  else if (ma == "tab") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::TABULATION;
  }
  else if (ma == "ins") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::INST_GEN;
  }
  else {
  error: USER_ERROR("bad test id " + _testId.actualValue);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == vstring::npos) { // not found
    goto error;
  }
  vstring timeString = testId.substr(index+1);
  _timeLimitInDeciseconds.set(timeString);

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
  vstring sel = testId.substr(0,index);
  _selection.set(sel);
  testId = testId.substr(index+1);

  if (testId == "") {
    goto error;
  }

  index = testId.find('_');
  vstring awr = testId.substr(0,index);
  _ageWeightRatio.readRatio(awr.c_str());
  if (index==string::npos) {
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

  readOptionsString(_forcedOptions.actualValue);

  // Also set the options forced by mode
  switch (_mode.actualValue) {
  case Mode::CASC:
  case Mode::CASC_LTB:
    _outputAxiomNames.actualValue = true;
    _proof.actualValue = Proof::TPTP;
    break;
  default:
    break;
  }
}

/**
 * Return testId vstring that represents current values of the options
 */
vstring Options::generateTestId() const
{
  CALL("Options::generateTestId");

  vostringstream res;
  //saturation algorithm
  res << ( (saturationAlgorithm()==SaturationAlgorithm::DISCOUNT) ? "dis" : ( (saturationAlgorithm()==SaturationAlgorithm::LRS) ? "lrs" : "ott") );

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
  /*Options cur=*this;
  bool first=true;
  static Set<AbstractOptionValue> forbidden;
  //we initialize the set if there's nothing inside
  if (forbidden.size()==0) {
    //things we output elsewhere
    forbidden.insert(_saturationAlgorithm);
    forbidden.insert(_selected);
    forbidden.insert(_ageWeightRatio);
    forbidden.insert(_timeLimit);

    //things we don't want to output
    forbidden.insert(_mode);
    forbidden.insert(_testId);
    forbidden.insert(_include);
    forbidden.insert(_problemName);
    forbidden.insert(_inputFile);
  }
*/
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
//TODO fix code
/*
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
*/
}


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
  if (_sineSelection.actualValue != SineSelection::OFF) return false;

  switch (_saturationAlgorithm.actualValue) {
  case SaturationAlgorithm::TABULATION: return false;
  case SaturationAlgorithm::INST_GEN: return true; // !!! Implies InstGen is always complete
  default: break;
  }

  // preprocessing for resolution-based algorithms
  if (_sos.actualValue != Sos::OFF) return false;
  // run-time rule causing incompleteness
  if (_forwardLiteralRewriting.actualValue) return false;
  
  bool unitEquality = prop.category() == Property::UEQ;
  bool hasEquality = (prop.equalityAtoms() != 0);

  if (!unitEquality) {
    if (_selection.actualValue <= -100 || _selection.actualValue >= 100) return false;
    if (_literalComparisonMode.actualValue == LiteralComparisonMode::REVERSE) return false;
  }

  if (!hasEquality) {
    if (_binaryResolution.actualValue) return true;
    if (_unitResultingResolution.actualValue==URResolution::EC_ONLY) return false;
    // binary resolution is off
    return prop.category() == Property::HNE; // URR is complete for Horn problems
  }

  // equality problems
  switch (_equalityProxy.actualValue) {
  case EqualityProxy::R: return false;
  case EqualityProxy::RS: return false;
  case EqualityProxy::RST: return false;
  default: break;
  }
  if (!_demodulationRedundancyCheck.actualValue) return false;
  if (_equalityResolutionWithDeletion.actualValue != RuleActivity::INPUT_ONLY) return false;
  if (!_superpositionFromVariables.actualValue) return false;

  // only checking resolution rules remain
  bool pureEquality = (prop.atoms() == prop.equalityAtoms());
  if (pureEquality) return true;
  if (_binaryResolution.actualValue) return true;
  if (_unitResultingResolution.actualValue==URResolution::EC_ONLY) return false;
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
  if (_sineSelection.actualValue != SineSelection::OFF) return false;

  switch (_saturationAlgorithm.actualValue) {
  case SaturationAlgorithm::TABULATION: return false;
  case SaturationAlgorithm::INST_GEN: return true; // !!!
  default: break;
  }

  // preprocessing for resolution-based algorithms
  if (_sos.actualValue != Sos::OFF) return false;
  // run-time rule causing incompleteness
  if (_forwardLiteralRewriting.actualValue) return false;
  
  if (_selection.actualValue <= -100 || _selection.actualValue >= 100) return false;

  return _binaryResolution.actualValue;
} // Options::completeForNNE

template<typename T>
vstring Options::RequiresCompleteForNonHorn<T>::check(OptionValue<T>& value){
  if(!env.options->completeForNNE()){
    return value.longName + " can only be used with a strategy complete for non-Horn problems without equality";
  }
  return 0;
}

/**
 * Check constraints necessary for options to make sense
 *
 * The function is called after all options are parsed.
 */
void Options::checkGlobalOptionConstraints() const
{
  CALL("Options::checkGlobalOptionsConstraints");

  VirtualIterator<AbstractOptionValue*> options = _lookup.values();
  while(options.hasNext()){ options.next()->checkConstraints(); }

}

/**
 * Check whether the option values make sense with respect to the given problem
 **/
void Options::checkProblemOptionConstraints(const Problem& prb) const
{
   CALL("Options::checkProblemOptionConstraints");

  Property& prop = *prb.getProperty();

  VirtualIterator<AbstractOptionValue*> options = _lookup.values();
  while(options.hasNext()){ options.next()->checkProblemConstraints(prop); }

}
