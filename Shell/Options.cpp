
/*
 * File Options.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Options.cpp
 * Implements Vampire options.
 *
 * @since 06/06/2001 Manchester, completely rewritten
 *
 * @since Sep 14 rewritten by Giles
 *
 *
 * IMPORTANT --> see .hpp file for instructions on how to add an option
 */

// Visual does not know the round function
#include <cmath>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"
#include "Debug/Assertion.hpp"

#include "Lib/VString.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/System.hpp"

#include "Shell/UIHelper.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Options.hpp"
#include "Property.hpp"

using namespace Lib;
using namespace Shell;

/**
 * Initialize options to the default values.
 *
 * Options are divided by the mode they are applicable to.
 * We then divid by tags where appropriate.
 * If an option is applicable to multiple modes but is not global it should be
 *  put in the most obvious mode - usually Vampire.
 *
 * IMPORTANT --> see .hpp file for instructions on how to add an option
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()

{
    CALL("Options::Options");
    init();
}

void Options::Options::init()
{
   CALL("Options::init");

   BYPASSING_ALLOCATOR; // Necessary because of use of std::function

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
#if !__APPLE__ && !__CYGWIN__
    _memoryLimit.addHardConstraint(lessThanEq((unsigned)Lib::System::getSystemMemory()));
#endif

    _mode = ChoiceOptionValue<Mode>("mode","",Mode::VAMPIRE,
                                    {"axiom_selection",
                                        "casc",
                                        "casc_sat",
                                        "casc_ltb",
                                        "clausify",
                                        "consequence_elimination",
                                        "grounding",
                                        "model_check",
                                        "output",
                                        "portfolio",
                                        "preprocess",
                                        "preprocess2",
                                        "profile",
                                        "random_strategy",
                                        "sat_solver",
                                        "smtcomp",
                                        "spider",
                                        "tclausify",
                                        "tpreprocess",
                                        "vampire"});
    _mode.description=
    "Select the mode of operation. Choices are:\n"
    "  -vampire: the standard mode of operation for first-order theorem proving\n"
    "  -portfolio: a portfolio mode running a specified schedule (see schedule)\n"
    "  -casc, casc_sat, smtcomp - like portfolio mode, with competition specific presets for schedule, etc.\n"
    "  -preprocess,axiom_selection,clausify,grounding: modes for producing output\n   for other solvers.\n"
    "  -tpreprocess,tclausify: output modes for theory input"
    "  -output,profile: output information about the problem\n"
    "  -sat_solver: accepts problems in DIMACS and uses the internal sat solver\n   directly\n"
    "Some modes are not currently maintained:\n"
    "  -bpa: perform bound propagation\n"
    "  -consequence_elimination: perform consequence elimination\n"
    "  -random_strategy: attempts to randomize the option values\n";
    _lookup.insert(&_mode);
    _mode.addHardConstraint(If(equal(Mode::CONSEQUENCE_ELIMINATION)).then(_splitting.is(notEqual(true))));

    _schedule = ChoiceOptionValue<Schedule>("schedule","sched",Schedule::CASC,
        {"casc",
         "casc_2014",
         "casc_2014_epr",
         "casc_2016",
         "casc_2017",
         "casc_2018",
         "casc_2019",
         "casc_sat",
         "casc_sat_2014",
         "casc_sat_2016",
         "casc_sat_2017",
         "casc_sat_2018",
         "casc_sat_2019",
         "ltb_2014",
         "ltb_2014_mzr",
         "ltb_default_2017",
         "ltb_hh4_2015_fast",
         "ltb_hh4_2015_midd",
         "ltb_hh4_2015_slow",
         "ltb_hh4_2017",
         "ltb_hll_2015_fast",
         "ltb_hll_2015_midd",
         "ltb_hll_2015_slow",
         "ltb_hll_2017",
         "ltb_isa_2015_fast",
         "ltb_isa_2015_midd",
         "ltb_isa_2015_slow",
         "ltb_isa_2017",
         "ltb_mzr_2015_fast",
         "ltb_mzr_2015_midd",
         "ltb_mzr_2015_slow",
         "ltb_mzr_2017",
         "smtcomp",
         "smtcomp_2016",
         "smtcomp_2017",
         "smtcomp_2018"});
    _schedule.description = "Schedule to be run by the portfolio mode.";
    _lookup.insert(&_schedule);
    _schedule.reliesOnHard(_mode.is(equal(Mode::CASC)->
        Or(_mode.is(equal(Mode::CASC_SAT)))->
        Or(_mode.is(equal(Mode::SMTCOMP)))->
        Or(_mode.is(equal(Mode::PORTFOLIO)))));

    _multicore = UnsignedOptionValue("cores","",1);
    _multicore.description = "When running in portfolio mode mode specify the number of cores, set to 0 to use maximum";
    _lookup.insert(&_multicore);
    _multicore.reliesOnHard(_mode.is(equal(Mode::CASC)->
        Or(_mode.is(equal(Mode::CASC_SAT)))->
        Or(_mode.is(equal(Mode::SMTCOMP)))->
        Or(_mode.is(equal(Mode::PORTFOLIO)))));

    _ltbLearning = ChoiceOptionValue<LTBLearning>("ltb_learning","ltbl",LTBLearning::OFF,{"on","off","biased"});
    _ltbLearning.description = "Perform learning in LTB mode";
    _lookup.insert(&_ltbLearning);
    _ltbLearning.setExperimental();

    _ltbDirectory = StringOptionValue("ltb_directory","","");
    _ltbDirectory.description = "Directory for output from LTB mode. Default is to put output next to problem.";
    _lookup.insert(&_ltbDirectory);

    _decode = DecodeOptionValue("decode","",this);
    _decode.description="Decodes an encoded strategy. Can be used to replay a strategy. To make Vampire output an encoded version of the strategy use the encode option.";
    _lookup.insert(&_decode);
    _decode.tag(OptionTag::DEVELOPMENT);

    _encode = BoolOptionValue("encode","",false);
    _encode.description="Output an encoding of the strategy to be used with the decode option";
    _lookup.insert(&_encode);
    _encode.tag(OptionTag::DEVELOPMENT);

    _randomStrategy = ChoiceOptionValue<RandomStrategy>("random_strategy","",RandomStrategy::OFF,{"on","off","sat","nocheck"});
    _randomStrategy.description =
      "Create a random strategy. Randomisation will occur after all other options have been "
      "set, whatever order they have been given in. A random number of options will be selected "
      " and set with a safe (possibly default) value.";
    _lookup.insert(&_randomStrategy);
    _randomStrategy.reliesOnHard(_mode.is(equal(Mode::VAMPIRE)->Or(_mode.is(equal(Mode::RANDOM_STRATEGY)))));
    _randomStrategy.tag(OptionTag::DEVELOPMENT);

    _forbiddenOptions = StringOptionValue("forbidden_options","","");
    _forbiddenOptions.description=
    "If some of the specified options are set to a forbidden state, vampire will fail to start, or in the CASC mode it will skip such strategies. The expected syntax is <opt1>=<val1>:<opt2>:<val2>:...:<optn>=<valN>";
    _lookup.insert(&_forbiddenOptions);
    _forbiddenOptions.tag(OptionTag::INPUT);

    _forcedOptions = StringOptionValue("forced_options","","");
    _forcedOptions.description=
    "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the option values set by other means (also inside CASC mode strategies)";
    _lookup.insert(&_forcedOptions);
    _forcedOptions.tag(OptionTag::INPUT);

    _printAllTheoryAxioms = BoolOptionValue("print_theory_axioms","",false);
    _printAllTheoryAxioms.description = "Just print all theory axioms and terminate";
    _printAllTheoryAxioms.tag(OptionTag::DEVELOPMENT);
    _lookup.insert(&_printAllTheoryAxioms);
    _printAllTheoryAxioms.setExperimental();

    _showHelp = BoolOptionValue("help","h",false);
    _showHelp.description="Display this help";
    _lookup.insert(&_showHelp);
    _showHelp.tag(OptionTag::HELP);

    _showOptions = BoolOptionValue("show_options","",false);
    _showOptions.description="List all available options";
    _lookup.insert(&_showOptions);
    _showOptions.tag(OptionTag::HELP);

    _showExperimentalOptions = BoolOptionValue("show_experimental_options","",false);
    _showExperimentalOptions.description="Include experimental options in showOption";
    _lookup.insert(&_showExperimentalOptions);
    _showExperimentalOptions.setExperimental(); // only we know about it!
    _showExperimentalOptions.tag(OptionTag::HELP);

    _explainOption = StringOptionValue("explain_option","explain","");
    _explainOption.description = "Use to explain a single option i.e. -explain explain";
    _lookup.insert(&_explainOption);
    _explainOption.tag(OptionTag::HELP);

    _ignoreMissing = ChoiceOptionValue<IgnoreMissing>("ignore_missing","",IgnoreMissing::OFF,{"on","off","warn"});
    _ignoreMissing.description=
    "Ignore any options that have been removed (useful in CASC mode where this can cause errors)";
    _lookup.insert(&_ignoreMissing);
    _ignoreMissing.tag(OptionTag::DEVELOPMENT);

    _badOption = ChoiceOptionValue<BadOption>("bad_option","",BadOption::SOFT,{"hard","forced","off","soft"});
    _badOption.description = "What should be done if a bad option value (wrt hard and soft constraints) is encountered:\n"
       " - hard: will cause a user error\n"
       " - soft: will only report the error (unless it is unsafe)\n"
       " - forced: <under development> \n" 
       " - off: will ignore safe errors\n"
       "Note that unsafe errors will aways lead to a user error";
    _lookup.insert(&_badOption);
    _badOption.tag(OptionTag::HELP);


    _namePrefix = StringOptionValue("name_prefix","","");
    _namePrefix.description=
    "Prefix for symbols introduced by Vampire (naming predicates, Skolem functions)";
    _lookup.insert(&_namePrefix);
    _namePrefix.tag(OptionTag::OUTPUT);

    // Do we really need to be able to set this externally?
    _problemName = StringOptionValue("problem_name","","");
    _problemName.description="";
    //_lookup.insert(&_problemName);

    _proof = ChoiceOptionValue<Proof>("proof","p",Proof::ON,{"off","on","proofcheck","tptp","property"});
    _proof.description=
    "Specifies whether proof will be output. 'proofcheck' will output proof as a sequence of TPTP problems to allow for proof-checking.";
    _lookup.insert(&_proof);
    _proof.tag(OptionTag::OUTPUT);

    _minimizeSatProofs = BoolOptionValue("minimize_sat_proofs","",true);
    _minimizeSatProofs.description="Perform unsat core minimization when a sat solver finds a clause set UNSAT\n"
        "(such as with AVATAR proofs or with global subsumption).";
    _lookup.insert(&_minimizeSatProofs);

    _proofExtra = ChoiceOptionValue<ProofExtra>("proof_extra","",ProofExtra::OFF,{"off","free","full"});
    _proofExtra.description="Add extra detail to proofs. "
      "When 'free' this uses known information only. " 
      "When 'full' this is allowed to perform expensive operations to acheive this so may"
      " significantly impact on performance. The option is experimental and the format "
      "of extra information may change between minor releases";
    _lookup.insert(&_proofExtra);

    _proofChecking = BoolOptionValue("proof_checking","",false);
    _proofChecking.description="";
    _lookup.insert(&_proofChecking);
    _proofChecking.setExperimental(); // don't think it works!

    _protectedPrefix = StringOptionValue("protected_prefix","","");
    _protectedPrefix.description="Symbols with this prefix are immune against elimination during preprocessing";
    _lookup.insert(&_protectedPrefix);
    _protectedPrefix.tag(OptionTag::PREPROCESSING);
    _protectedPrefix.setExperimental(); // Does not work for all (any?) preprocessing steps currently

    _statistics = ChoiceOptionValue<Statistics>("statistics","stat",Statistics::BRIEF,{"brief","full","none"});
    _statistics.description="The level of statistics to report at the end of the run.";
    _lookup.insert(&_statistics);
    _statistics.tag(OptionTag::OUTPUT);

    _testId = StringOptionValue("test_id","","unspecified_test");
    _testId.description="";
    _lookup.insert(&_testId);
    _testId.setExperimental();

    _outputMode = ChoiceOptionValue<Output>("output_mode","om",Output::SZS,{"smtcomp","spider","szs","vampire"});
    _outputMode.description="";
    _lookup.insert(&_outputMode);
    _outputMode.setExperimental();

    _thanks = StringOptionValue("thanks","","Tanya");
    _thanks.description="";
    _lookup.insert(&_thanks);
    _thanks.setExperimental();

    _timeLimitInDeciseconds = TimeLimitOptionValue("time_limit","t",600); // stores deciseconds, but reads seconds from the user by default
    _timeLimitInDeciseconds.description="Time limit in wall clock seconds, you can use d,s,m,h,D suffixes also i.e. 60s, 5m. Setting it to 0 effectively gives no time limit.";
    _lookup.insert(&_timeLimitInDeciseconds);

    _timeStatistics = BoolOptionValue("time_statistics","tstat",false);
    _timeStatistics.description="Show how much running time was spent in each part of Vampire";
    _lookup.insert(&_timeStatistics);
    _timeStatistics.tag(OptionTag::OUTPUT);

//*********************** Input  ***********************

    _include = StringOptionValue("include","","");
    _include.description="Path prefix for the 'include' TPTP directive";
    _lookup.insert(&_include);
    _include.tag(OptionTag::INPUT);

    _inputFile= InputFileOptionValue("input_file","","",this);
    _inputFile.description="Problem file to be solved (if not specified, standard input is used)";
    _lookup.insert(&_inputFile);
    _inputFile.tag(OptionTag::INPUT);
    _inputFile.setExperimental();

    _inputSyntax= ChoiceOptionValue<InputSyntax>("input_syntax","",
                                                 //in case we compile vampire with bpa, then the default input syntax is smtlib
#if !GNUMP
                                                 InputSyntax::TPTP,
#else
                                                 InputSyntax::SMTLIB,
#endif
                                                 {"simplify","smtlib","smtlib2","tptp"});//,"xhuman","xmps","xnetlib"});
    _inputSyntax.description="Input syntax. Only TPTP is actively maintained.";
    _lookup.insert(&_inputSyntax);
    _inputSyntax.tag(OptionTag::INPUT);

    _smtlibConsiderIntsReal = BoolOptionValue("smtlib_consider_ints_real","",false);
    _smtlibConsiderIntsReal.description="all integers will be considered to be reals by the SMTLIB parser";
    _lookup.insert(&_smtlibConsiderIntsReal);
    _smtlibConsiderIntsReal.setExperimental();
    _smtlibConsiderIntsReal.tag(OptionTag::INPUT);

    _smtlibFletAsDefinition = BoolOptionValue("smtlib_flet_as_definition","",false);
    _smtlibFletAsDefinition.description="";
    _lookup.insert(&_smtlibFletAsDefinition);
    _smtlibFletAsDefinition.setExperimental();
    _smtlibFletAsDefinition.tag(OptionTag::INPUT);

    _guessTheGoal = ChoiceOptionValue<GoalGuess>("guess_the_goal","gtg",GoalGuess::OFF,{"off","all","exists_top","exists_all","exists_sym","position"});
    _guessTheGoal.description = "Use heuristics to guess formulas that correspond to the goal. Doesn't "
                                "really make sense if there is already a goal.";
    _lookup.insert(&_guessTheGoal);
    _guessTheGoal.tag(OptionTag::INPUT);
    _guessTheGoal.setExperimental();

    _guessTheGoalLimit = UnsignedOptionValue("guess_the_goal_limit","gtgl",1);
    _guessTheGoalLimit.description = "The maximum number of input units a symbol appears for it to be considered in a goal";
    _guessTheGoalLimit.tag(OptionTag::INPUT);
    _guessTheGoalLimit.setExperimental();
    //_guessTheGoalLimit.reliesOn(_guessTheGoal.is(equal(true)));
    _lookup.insert(&_guessTheGoalLimit);


//*********************** Preprocessing  ***********************

    _ignoreConjectureInPreprocessing = BoolOptionValue("ignore_conjecture_in_preprocessing","icip",false);
    _ignoreConjectureInPreprocessing.description="Make sure we do not delete the conjecture in preprocessing";
    _lookup.insert(&_ignoreConjectureInPreprocessing);
    _ignoreConjectureInPreprocessing.tag(OptionTag::PREPROCESSING);

    _inequalitySplitting = IntOptionValue("inequality_splitting","ins",0);
    _inequalitySplitting.description=
    "Defines a weight threshold w such that any clause C \\/ s!=t where s (or conversely t) is ground "
    "and has weight less than w is replaced by C \\/ p(s) with the additional clause ~p(t) being added "
    "for fresh predicate p.";
    _lookup.insert(&_inequalitySplitting);
    _inequalitySplitting.tag(OptionTag::PREPROCESSING);

    //TODO randomly switch to different values for testing?

    _sos = ChoiceOptionValue<Sos>("sos","sos",Sos::OFF,{"all","off","on","theory"});
    _sos.description=
    "Set of support strategy. All formulas annotated as axioms are put directly among active clauses, without performing any inferences between them. If all, select all literals of set-of-support clauses, ortherwise use the default literal selector.";
    _lookup.insert(&_sos);
    _sos.tag(OptionTag::PREPROCESSING);
    _sos.setRandomChoices(And(isRandSat(),saNotInstGen()),{"on","off","off","off","off"});
    _sos.setRandomChoices(And(isRandOn(),hasNonUnits()),{"on","off","off","off","off"});
    _sos.setRandomChoices(isRandOn(),{"all","off","on"});

    _sosTheoryLimit = UnsignedOptionValue("sos_theory_limit","sstl",0);
    _sosTheoryLimit.description="When sos=theory the depth of descendants a theory axiom can have";
    _sosTheoryLimit.setExperimental();
    _lookup.insert(&_sosTheoryLimit);
    _sosTheoryLimit.tag(OptionTag::PREPROCESSING);
    _sosTheoryLimit.reliesOn(_sos.is(equal(Sos::THEORY)));



    _equalityProxy = ChoiceOptionValue<EqualityProxy>( "equality_proxy","ep",EqualityProxy::OFF,{"R","RS","RST","RSTC","off"});
    _equalityProxy.description="Aplies the equality proxy transformation to the problem. It works as follows:\n"
     " - All literals s=t are replaced by E(s,t)\n"
     " - All literals s!=t are replaced by ~E(s,t)\n"
     " - If S the symmetry clause ~E(x,y) \\/ E(y,x) is added\n"
     " - If T the transitivity clause ~E(x,y) \\/ ~E(y,z) \\/ E(x,z) is added\n"
     " - If C the congruence clauses are added as follows:\n"
     "    for predicates p that are not E or equality add\n"
     "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ ~p(x1,...,xN) \\/ p(y1,...,yN)\n"
     "    for non-constant functions f add\n"
     "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ E(f(x1,...,xN),f(y1,...,yN))\n"
     " R stands for reflexivity";
    _lookup.insert(&_equalityProxy);
    _equalityProxy.tag(OptionTag::PREPROCESSING);
    _equalityProxy.addProblemConstraint(hasEquality());
    _equalityProxy.setRandomChoices(isRandOn(),{"R","RS","RST","RSTC","off","off","off","off","off"}); // wasn't tested, make off more likely
    

    _equalityResolutionWithDeletion = ChoiceOptionValue<RuleActivity>( "equality_resolution_with_deletion","erd",
                                                                      RuleActivity::INPUT_ONLY,{"input_only","off","on"});
    _equalityResolutionWithDeletion.description="Perform equality resolution with deletion. Only input_only and off are valid options.";
    _lookup.insert(&_equalityResolutionWithDeletion);
    _equalityResolutionWithDeletion.tag(OptionTag::PREPROCESSING);
    _equalityResolutionWithDeletion.addConstraint(notEqual(RuleActivity::ON));
    //TODO does this depend on anything?
    //TODO is there a problemConstraint?
    _equalityResolutionWithDeletion.setRandomChoices({"input_only","off"});


    _arityCheck = BoolOptionValue("arity_check","",false);
    _arityCheck.description="Enforce the condition that the same symbol name cannot be used with multiple arities."
       "This also ensures a symbol is not used as a function and predicate.";
    _lookup.insert(&_arityCheck);
    _arityCheck.tag(OptionTag::DEVELOPMENT);
    
    _functionDefinitionElimination = ChoiceOptionValue<FunctionDefinitionElimination>("function_definition_elimination","fde",
                                                                                      FunctionDefinitionElimination::ALL,{"all","none","unused"});
    _functionDefinitionElimination.description=
    "Attempts to eliminate function definitions. A function definition is a unit clause of the form f(x1,..,xn) = t where x1,..,xn are the pairwise distinct free variables of t and f does not appear in t. If 'all', definitions are eliminated by replacing every occurence of f(s1,..,sn) by t{x1 -> s1, .., xn -> sn}. If 'unused' only unused definitions are removed.";
    _lookup.insert(&_functionDefinitionElimination);
    _functionDefinitionElimination.tag(OptionTag::PREPROCESSING);
    _functionDefinitionElimination.addProblemConstraint(hasEquality());
    _functionDefinitionElimination.setRandomChoices({"all","none"});

    _generalSplitting = ChoiceOptionValue<RuleActivity>("general_splitting","gsp",RuleActivity::OFF,{"input_only","off","on"});
    _generalSplitting.description=
    "Splits clauses in order to reduce number of different variables in each clause. "
    "A clause C[X] \\/ D[Y] with subclauses C and D over non-equal sets of variables X and Y can be split into S(Z) \\/ C[X] and ~S(Z) \\/ D[Y] where Z is the intersection of X and Y. "
    " Only input_only and off are valid values.";
    _lookup.insert(&_generalSplitting);
    _generalSplitting.tag(OptionTag::PREPROCESSING);
    _generalSplitting.addConstraint(notEqual(RuleActivity::ON));
    _generalSplitting.addProblemConstraint(hasNonUnits());
    _generalSplitting.setRandomChoices({"off","input_only"});

    _unusedPredicateDefinitionRemoval = BoolOptionValue("unused_predicate_definition_removal","updr",true);
    _unusedPredicateDefinitionRemoval.description="Attempt to remove predicate definitions. A predicate definition is a formula of the form ![X1,..,Xn] : (p(X1,..,XN) <=> F) where p is not equality and does not occur in F and X1,..,XN are the free variables of F. If p has only positive (negative) occurences then <=> in the definition can be replaced by => (<=). If p does not occur in the rest of the problem the definition can be removed.";
    _lookup.insert(&_unusedPredicateDefinitionRemoval);
    _unusedPredicateDefinitionRemoval.tag(OptionTag::PREPROCESSING);
    _unusedPredicateDefinitionRemoval.addProblemConstraint(notWithCat(Property::UEQ));
    _unusedPredicateDefinitionRemoval.setRandomChoices({"on","off"});

    _blockedClauseElimination = BoolOptionValue("blocked_clause_elimination","bce",false);
    _blockedClauseElimination.description="Eliminate blocked clauses after clausification.";
    _lookup.insert(&_blockedClauseElimination);
    _blockedClauseElimination.tag(OptionTag::PREPROCESSING);
    _blockedClauseElimination.addProblemConstraint(notWithCat(Property::UEQ));
    _blockedClauseElimination.setRandomChoices({"on","off"});

    _theoryAxioms = ChoiceOptionValue<TheoryAxiomLevel>("theory_axioms","tha",TheoryAxiomLevel::ON,{"on","off","some"});
    _theoryAxioms.description="Include theory axioms for detected interpreted symbols";
    _lookup.insert(&_theoryAxioms);
    _theoryAxioms.tag(OptionTag::PREPROCESSING);

    _theoryFlattening = BoolOptionValue("theory_flattening","thf",false);
    _theoryFlattening.description = "Flatten clauses to separate theory and non-theory parts";
    _lookup.insert(&_theoryFlattening);
    _theoryFlattening.tag(OptionTag::PREPROCESSING);
    _theoryFlattening.setExperimental();

    _sineDepth = UnsignedOptionValue("sine_depth","sd",0);
    _sineDepth.description=
    "Limit number of iterations of the transitive closure algorithm that selects formulas based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal limit (least selected axioms), 2 allows two iterations, etc...";
    _lookup.insert(&_sineDepth);
    _sineDepth.tag(OptionTag::PREPROCESSING);
    // Captures that if the value is not default then sineSelection must be on
    _sineDepth.reliesOn(_sineSelection.is(notEqual(SineSelection::OFF)));
    _sineDepth.setRandomChoices({"0","1","2","3","4","5","7","10"});

    _sineGeneralityThreshold = UnsignedOptionValue("sine_generality_threshold","sgt",0);
    _sineGeneralityThreshold.description=
    "Generality of a symbol is the number of input formulas in which a symbol appears. If the generality of a symbol is smaller than the threshold, it is always added into the D-relation with formulas in which it appears.";
    _lookup.insert(&_sineGeneralityThreshold);
    _sineGeneralityThreshold.tag(OptionTag::PREPROCESSING);
    // Captures that if the value is not default then sineSelection must be on
    _sineGeneralityThreshold.reliesOn(_sineSelection.is(notEqual(SineSelection::OFF)));

    _sineSelection = ChoiceOptionValue<SineSelection>("sine_selection","ss",SineSelection::OFF,{"axioms","included","off"});
    _sineSelection.description=
    "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) are initially selected, and the SInE selection is performed on those annotated as 'axiom'. If 'included', all formulas that are directly in the problem file are initially selected, and the SInE selection is performed on formulas from included files. The 'included' value corresponds to the behaviour of the original SInE implementation.";
    _lookup.insert(&_sineSelection);
    _sineSelection.tag(OptionTag::PREPROCESSING);
    _sineSelection.setRandomChoices(atomsMoreThan(100000),{"axioms","axioms","off"});
    _sineSelection.setRandomChoices(atomsMoreThan(30000),{"axioms","off"});
    _sineSelection.setRandomChoices(atomsMoreThan(10000),{"axioms","off","off","off"});
    _sineSelection.setRandomChoices(atomsMoreThan(3000),{"axioms","off","off","off","off","off"});
    _sineSelection.setRandomChoices(atomsMoreThan(1000),{"axioms","off","off","off","off","off","off","off"});

    _sineTolerance = FloatOptionValue("sine_tolerance","st",1.0);
    _sineTolerance.description="SInE tolerance parameter (sometimes referred to as 'benevolence')";
    _lookup.insert(&_sineTolerance);
    _sineTolerance.tag(OptionTag::PREPROCESSING);
    _sineTolerance.addConstraint(equal(0.0f)->Or(greaterThanEq(1.0f) ));
    // Captures that if the value is not 1.0 then sineSelection must be on
    _sineTolerance.reliesOn(_sineSelection.is(notEqual(SineSelection::OFF)));
    _sineTolerance.setRandomChoices({"1.0","1.2","1.5","2.0","3.0","5.0"});

    _naming = IntOptionValue("naming","nm",8);
    _naming.description="Introduce names for subformulas. Given a subformula F(x1,..,xk) of formula G a new predicate symbol is introduced as a name for F(x1,..,xk) by adding the axiom n(x1,..,xk) <=> F(x1,..,xk) and replacing F(x1,..,xk) with n(x1,..,xk) in G. The value indicates how many times a subformula must be used before it is named.";
    _lookup.insert(&_naming);
    _naming.tag(OptionTag::PREPROCESSING);
    _naming.addHardConstraint(lessThan(32768));
    _naming.addHardConstraint(greaterThan(-1));
    _naming.addHardConstraint(notEqual(1));

    _newCNF = BoolOptionValue("newcnf","",false);
    _newCNF.description="Use NewCNF algorithm to do naming, preprecess3 and clausificiation.";
    _lookup.insert(&_newCNF);
    _newCNF.tag(OptionTag::PREPROCESSING);

    _iteInliningThreshold = IntOptionValue("ite_inlining_threshold","", 0);
    _iteInliningThreshold.description="Threashold of inlining of if-then-else expressions. "
                                      "0 means that all expressions are named. "
                                      "<0 means that all expressions are inlined.";
    _lookup.insert(&_iteInliningThreshold);
    _iteInliningThreshold.tag(OptionTag::PREPROCESSING);

    _inlineLet = BoolOptionValue("inline_let","ile",false);
    _inlineLet.description="Always inline let-expressions.";
    _lookup.insert(&_inlineLet);
    _inlineLet.tag(OptionTag::PREPROCESSING);


//*********************** Output  ***********************

    // how is this used?
    _logFile = StringOptionValue("log_file","","off");
    _logFile.description="";
    //_lookup.insert(&_logFile);
    _logFile.tag(OptionTag::OUTPUT);

    //used?
    _xmlOutput = StringOptionValue("xml_output","","off");
    _xmlOutput.description="File to put XML output in.";
    //_lookup.insert(&_xmlOutput);
    _xmlOutput.tag(OptionTag::OUTPUT);

    _latexOutput = StringOptionValue("latex_output","","off");
    _latexOutput.description="File that will contain proof in the LaTeX format.";
    _lookup.insert(&_latexOutput);
    _latexOutput.tag(OptionTag::OUTPUT);

    _latexUseDefaultSymbols = BoolOptionValue("latex_use_default_symbols","",true);
    _latexUseDefaultSymbols.description="Interpretted symbols such as product have default LaTeX symbols"
        " that can be used. They can be overriden in the normal way. This option can turn them off";
    _latexUseDefaultSymbols.tag(OptionTag::OUTPUT);
    _lookup.insert(&_latexUseDefaultSymbols);

    _outputAxiomNames = BoolOptionValue("output_axiom_names","",false);
    _outputAxiomNames.description="Preserve names of axioms from the problem file in the proof output";
    _lookup.insert(&_outputAxiomNames);
    _outputAxiomNames.tag(OptionTag::OUTPUT);


    _printClausifierPremises = BoolOptionValue("print_clausifier_premises","",false);
    _printClausifierPremises.description="Output how the clausified problem was derived.";
    _lookup.insert(&_printClausifierPremises);
    _printClausifierPremises.tag(OptionTag::OUTPUT);

    _showAll = BoolOptionValue("show_everything","",false);
    _showAll.description="Turn (almost) all of the showX commands on";
    _lookup.insert(&_showAll);
    _showAll.tag(OptionTag::DEVELOPMENT);

    _showActive = BoolOptionValue("show_active","",false);
    _showActive.description="Print activated clauses.";
    _lookup.insert(&_showActive);
    _showActive.tag(OptionTag::DEVELOPMENT);

    _showBlocked = BoolOptionValue("show_blocked","",false);
    _showBlocked.description="Show generating inferences blocked due to coloring of symbols";
    _lookup.insert(&_showBlocked);
    _showBlocked.tag(OptionTag::DEVELOPMENT);

    _showDefinitions = BoolOptionValue("show_definitions","",false);
    _showDefinitions.description="Show definition introductions.";
    _lookup.insert(&_showDefinitions);
    _showDefinitions.tag(OptionTag::DEVELOPMENT);

    _showNew = BoolOptionValue("show_new","",false);
    _showNew.description="Show new (generated) clauses";
    _lookup.insert(&_showNew);
    _showNew.tag(OptionTag::DEVELOPMENT);

    _sineToAge = BoolOptionValue("sine_to_age","s2a",false);
    _lookup.insert(&_sineToAge);
    _sineToAge.tag(OptionTag::DEVELOPMENT);

    _sineToPredLevels = ChoiceOptionValue<PredicateSineLevels>("sine_to_pred_levels","s2pl",PredicateSineLevels::OFF,{"no","off","on"});
    _sineToPredLevels.description = "Assign levels to predicate symbols as they are used to trigger axioms during SInE computation. "
        "Then used then as predicateLevels determining the ordering. on means conjecture symbols are larger, no means the opposite. (equality keeps its standard lowest level).";
    _lookup.insert(&_sineToPredLevels);
    _sineToPredLevels.tag(OptionTag::DEVELOPMENT);
    _sineToPredLevels.addHardConstraint(If(notEqual(PredicateSineLevels::OFF)).then(_literalComparisonMode.is(notEqual(LiteralComparisonMode::PREDICATE))));
    _sineToPredLevels.addHardConstraint(If(notEqual(PredicateSineLevels::OFF)).then(_literalComparisonMode.is(notEqual(LiteralComparisonMode::REVERSE))));

    // Like generality threshold for SiNE, except used by the sine2age trick
    _sineToAgeGeneralityThreshold = UnsignedOptionValue("sine_to_age_generality_threshold","s2agt",0);
    _lookup.insert(&_sineToAgeGeneralityThreshold);
    _sineToAgeGeneralityThreshold.tag(OptionTag::DEVELOPMENT);
    _sineToAgeGeneralityThreshold.reliesOn(_sineToAge.is(equal(true)->Or(_sineToPredLevels.is(notEqual(PredicateSineLevels::OFF)))));

    // Like generality threshold for SiNE, except used by the sine2age trick
    _sineToAgeTolerance = FloatOptionValue("sine_to_age_tolerance","s2at",1.0);
    _lookup.insert(&_sineToAgeTolerance);
    _sineToAgeTolerance.tag(OptionTag::DEVELOPMENT);
    _sineToAgeTolerance.addConstraint(equal(0.0f)->Or(greaterThanEq(1.0f) ));
    // Captures that if the value is not 1.0 then sineSelection must be on
    _sineToAgeTolerance.reliesOn(_sineToAge.is(equal(true)->Or(_sineToPredLevels.is(notEqual(PredicateSineLevels::OFF)))));
    _sineToAgeTolerance.setRandomChoices({"1.0","1.2","1.5","2.0","3.0","5.0"});

    _showSplitting = BoolOptionValue("show_splitting","",false);
    _showSplitting.description="Show updates within AVATAR";
    _lookup.insert(&_showSplitting);
    _showSplitting.tag(OptionTag::DEVELOPMENT);

    _showNewPropositional = BoolOptionValue("show_new_propositional","",false);
    _showNewPropositional.description="";
    //_lookup.insert(&_showNewPropositional);
    _showNewPropositional.tag(OptionTag::DEVELOPMENT);

    _showNonconstantSkolemFunctionTrace = BoolOptionValue("show_nonconstant_skolem_function_trace","",false);
    _showNonconstantSkolemFunctionTrace.description="Show introduction of non-constant skolem functions.";
    _lookup.insert(&_showNonconstantSkolemFunctionTrace);
    _showNonconstantSkolemFunctionTrace.tag(OptionTag::DEVELOPMENT);


    _showPassive = BoolOptionValue("show_passive","",false);
    _showPassive.description="Show clauses added to the passive set.";
    _lookup.insert(&_showPassive);
    _showPassive.tag(OptionTag::DEVELOPMENT);
    
    _showReductions = BoolOptionValue("show_reductions","",false);
    _showReductions.description="Show reductions.";
    _showReductions.tag(OptionTag::DEVELOPMENT);
    _lookup.insert(&_showReductions);

    _showPreprocessing = BoolOptionValue("show_preprocessing","",false);
    _showPreprocessing.description="Show preprocessing.";
    _lookup.insert(&_showPreprocessing);
    _showPreprocessing.tag(OptionTag::DEVELOPMENT);

    _showSkolemisations = BoolOptionValue("show_skolemisations","",false);
    _showSkolemisations.description="Show Skolemisations.";
    _lookup.insert(&_showSkolemisations);
    _showSkolemisations.tag(OptionTag::DEVELOPMENT);

    _showSymbolElimination = BoolOptionValue("show_symbol_elimination","",false);
    _showSymbolElimination.description="Show symbol elimination.";
    _lookup.insert(&_showSymbolElimination);
    _showSymbolElimination.tag(OptionTag::DEVELOPMENT);

    _showTheoryAxioms = BoolOptionValue("show_theory_axioms","",false);
    _showTheoryAxioms.description="Show the added theory axioms.";
    _lookup.insert(&_showTheoryAxioms);
    _showTheoryAxioms.tag(OptionTag::DEVELOPMENT);

#if VZ3
    _showZ3 = BoolOptionValue("show_z3","",false);
    _showZ3.description="Print the clauses being added to Z3";
    _lookup.insert(&_showZ3);
    _showZ3.tag(OptionTag::DEVELOPMENT);
#endif

    _showFOOL = BoolOptionValue("show_fool","",false);
    _showFOOL.description="Reveal the internal representation of FOOL terms";
    _lookup.insert(&_showFOOL);
    _showFOOL.tag(OptionTag::OUTPUT);

    _showFMBsortInfo = BoolOptionValue("show_fmb_sort_info","",false);
    _showFMBsortInfo.description = "Print information about sorts in FMB";
    _lookup.insert(&_showFMBsortInfo);
    _showFMBsortInfo.tag(OptionTag::OUTPUT);

    _showInduction = BoolOptionValue("show_induction","",false);
    _showInduction.description = "Print information about induction";
    _lookup.insert(&_showInduction);
    _showInduction.tag(OptionTag::OUTPUT);

    _manualClauseSelection = BoolOptionValue("manual_cs","",false);
    _manualClauseSelection.description="Run Vampire interactively by manually picking the clauses to be selected";
    _lookup.insert(&_manualClauseSelection);
    _manualClauseSelection.tag(OptionTag::DEVELOPMENT);
    
//************************************************************************
//*********************** VAMPIRE (includes CASC)  ***********************
//************************************************************************

//*********************** Saturation  ***********************

    _saturationAlgorithm = ChoiceOptionValue<SaturationAlgorithm>("saturation_algorithm","sa",SaturationAlgorithm::LRS,
                                                                  {"discount","fmb","inst_gen","lrs","otter"
#if VZ3
      ,"z3"
#endif
    });
    _saturationAlgorithm.description=
    "Select the saturation algorithm:\n"
    " - discount:\n"
    " - otter:\n"
    " - limited resource:\n"
    " - instance generation: a simple implementation of instantiation calculus\n"
    "    (global_subsumption, unit_resulting_resolution and age_weight_ratio)\n"
    " - fmb : finite model building for satisfiable problems.\n"
    " -z3 : pass the preprocessed problem to z3, will terminate if the resulting problem is not ground.\n"
    "inst_gen, z3 and fmb aren't influenced by options for the saturation algorithm, apart from those under the relevant heading";
    _lookup.insert(&_saturationAlgorithm);
    _saturationAlgorithm.tag(OptionTag::SATURATION);
    // Captures that if the saturation algorithm is InstGen then splitting must be off
    _saturationAlgorithm.addHardConstraint(If(equal(SaturationAlgorithm::INST_GEN)).then(_splitting.is(notEqual(true))));
    // Note order of adding constraints matters (we assume previous gaurds are false)
    _saturationAlgorithm.setRandomChoices(isRandSat(),{"discount","otter","inst_gen","fmb"});
    _saturationAlgorithm.setRandomChoices(Or(hasCat(Property::UEQ),atomsLessThan(4000)),{"lrs","discount","otter","inst_gen"});
    _saturationAlgorithm.setRandomChoices({"discount","inst_gen","lrs","otter"});

#if VZ3
    _smtForGround = BoolOptionValue("smt_for_ground","smtfg",true);
    _smtForGround.description = "When a (theory) problem is ground after preprocessing pass it to Z3. In this case we can return sat if Z3 does.";
    _lookup.insert(&_smtForGround);
#endif


    _fmbNonGroundDefs = BoolOptionValue("fmb_nonground_defs","fmbngd",false);
    _fmbNonGroundDefs.description = "Introduce definitions for non ground terms in preprocessing for fmb";
    //_lookup.insert(&_fmbNonGroundDefs);
    _fmbNonGroundDefs.setExperimental();
    _fmbNonGroundDefs.setRandomChoices({"on","off"});

    _fmbStartSize = UnsignedOptionValue("fmb_start_size","fmbss",1);
    _fmbStartSize.description = "Set the initial model size for finite model building";
    _lookup.insert(&_fmbStartSize);
    _fmbStartSize.setExperimental();

    _fmbSymmetryRatio = FloatOptionValue("fmb_symmetry_ratio","fmbsr",1.0);
    _fmbSymmetryRatio.description = "";
    _lookup.insert(&_fmbSymmetryRatio);
    _fmbSymmetryRatio.setExperimental();

    _fmbSymmetryOrderSymbols = ChoiceOptionValue<FMBSymbolOrders>("fmb_symmetry_symbol_order","fmbsso",
                                                     FMBSymbolOrders::OCCURENCE,
                                                     {"occurence","input_usage","preprocessed_usage"}); 
    _fmbSymmetryOrderSymbols.description = "";
    _lookup.insert(&_fmbSymmetryOrderSymbols);
    _fmbSymmetryOrderSymbols.setExperimental();

    _fmbSymmetryWidgetOrders = ChoiceOptionValue<FMBWidgetOrders>("fmb_symmetry_widget_order","fmbswo",
                                                     FMBWidgetOrders::FUNCTION_FIRST,
                                                     {"function_first","argument_first","diagonal"});
    _fmbSymmetryWidgetOrders.description = "";
    _lookup.insert(&_fmbSymmetryWidgetOrders);
    _fmbSymmetryWidgetOrders.setExperimental();

    _fmbAdjustSorts = ChoiceOptionValue<FMBAdjustSorts>("fmb_adjust_sorts","fmbas",
                                                           FMBAdjustSorts::GROUP,
                                                           {"off","expand","group","predicate","function"});
    _fmbAdjustSorts.description = "Detect monotonic sorts. If <expand> then expand monotonic subsorts into proper sorts. If <group> then collapse monotonic sorts into a single sort. If <predicate> then introduce sort predicates for non-monotonic sorts and collapse all sorts into one. If <function> then introduce sort functions for non-monotonic sorts and collapse all sorts into one";
    _lookup.insert(&_fmbAdjustSorts);
    _fmbAdjustSorts.addHardConstraint(
      If(equal(FMBAdjustSorts::EXPAND)).then(_fmbEnumerationStrategy.is(notEqual(FMBEnumerationStrategy::CONTOUR))));

    _fmbDetectSortBounds = BoolOptionValue("fmb_detect_sort_bounds","fmbdsb",false);
    _fmbDetectSortBounds.description = "Use a saturation loop to detect sort bounds introduced by (for example) injective functions";
    _fmbDetectSortBounds.setExperimental();
    _lookup.insert(&_fmbDetectSortBounds);
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::PREDICATE))));
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::FUNCTION))));

    _fmbDetectSortBoundsTimeLimit = UnsignedOptionValue("fmb_detect_sort_bounds_time_limit","fmbdsbt",1);
    _fmbDetectSortBoundsTimeLimit.description = "The time limit (in seconds) for performing sort bound detection";
    _fmbDetectSortBoundsTimeLimit.setExperimental();
    _lookup.insert(&_fmbDetectSortBoundsTimeLimit);

    _fmbSizeWeightRatio = UnsignedOptionValue("fmb_size_weight_ratio","fmbswr",1);
    _fmbSizeWeightRatio.description = "Controls the priority the next sort size vector is given based on a ratio. 0 is size only, 1 means 1:1, 2 means 1:2, etc.";
    _fmbSizeWeightRatio.reliesOn(_fmbEnumerationStrategy.is(equal(FMBEnumerationStrategy::CONTOUR)));
    _fmbSizeWeightRatio.setExperimental();
    _lookup.insert(&_fmbSizeWeightRatio);

    _fmbEnumerationStrategy = ChoiceOptionValue<FMBEnumerationStrategy>("fmb_enumeration_strategy","fmbes",FMBEnumerationStrategy::SBMEAM,{"sbeam",
#if VZ3
        "smt",
#endif
        "contour"});
    _fmbEnumerationStrategy.description = "How model sizes assignments are enumerated in the multi-sorted setting. (Only smt and contour are known to be finite model complete and can therefore return UNSAT.)";
    _fmbEnumerationStrategy.setExperimental();
    _lookup.insert(&_fmbEnumerationStrategy);

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
    _selection.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<int>(_instGenWithResolution.is(equal(true))));
    _selection.setRandomChoices(And(isRandSat(),saNotInstGen()),{"0","1","2","3","4","10","11","-1","-2","-3","-4","-10","-11"});
    _selection.setRandomChoices({"0","1","2","3","4","10","11","1002","1003","1004","1010","1011","-1","-2","-3","-4","-10","-11","-1002","-1003","-1004","-1010"});

    _lookaheadDelay = IntOptionValue("lookahaed_delay","lsd",0);
    _lookaheadDelay.description = "Delay the use of lookahead selection by this many selections"
                                  " the idea is that lookahead selection may behave erratically"
                                  " at the start";
    _lookaheadDelay.tag(OptionTag::SATURATION);
    _lookup.insert(&_lookaheadDelay);
    _lookaheadDelay.reliesOn(_selection.isLookAheadSelection());
    
    _ageWeightRatio = RatioOptionValue("age_weight_ratio","awr",1,1,':');
    _ageWeightRatio.description=
    "Ratio in which clauses are being selected for activation i.e. a:w means that for every a clauses selected based on age "
    "there will be w selected based on weight.";
    _lookup.insert(&_ageWeightRatio);
    _ageWeightRatio.tag(OptionTag::SATURATION);
    _ageWeightRatio.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<int>(_instGenWithResolution.is(equal(true))));
    _ageWeightRatio.setRandomChoices({"8:1","5:1","4:1","3:1","2:1","3:2","5:4","1","2:3","2","3","4","5","6","7","8","10","12","14","16","20","24","28","32","40","50","64","128","1024"});


    _ageWeightRatioShape = ChoiceOptionValue<AgeWeightRatioShape>("age_weight_ratio_shape","awrs",AgeWeightRatioShape::CONSTANT,{"constant","decay", "converge"});
    _ageWeightRatioShape.description = "How to change the age/weight ratio during proof search.";
    _lookup.insert(&_ageWeightRatioShape);
    _ageWeightRatioShape.tag(OptionTag::SATURATION);

    _ageWeightRatioShapeFrequency = UnsignedOptionValue("age_weight_ratio_shape_frequency","awrsf",100);
    _ageWeightRatioShapeFrequency.description = "How frequently the age/weight ratio shape is to change: i.e. if set to 'decay' at a frequency of 100, the age/weight ratio will change every 100 age/weight choices.";
    _lookup.insert(&_ageWeightRatioShapeFrequency);
    _ageWeightRatioShapeFrequency.tag(OptionTag::SATURATION);

    _useTheorySplitQueues = BoolOptionValue("theory_split_queue","thsq",false);
    _useTheorySplitQueues.description = "Turn on clause selection using multiple queues containing different clauses (split by amount of theory reasoning)";
    _lookup.insert(&_useTheorySplitQueues);
    _useTheorySplitQueues.tag(OptionTag::SATURATION);

    _theorySplitQueueExpectedRatioDenom = IntOptionValue("theory_split_queue_expected_ratio_denom","thsqd", 8);
    _theorySplitQueueExpectedRatioDenom.description = "The denominator n such that we expect the final proof to have a ratio of theory-axioms to all-axioms of 1/n.";
    _lookup.insert(&_theorySplitQueueExpectedRatioDenom);
    _theorySplitQueueExpectedRatioDenom.reliesOn(_useTheorySplitQueues.is(equal(true)));
    _theorySplitQueueExpectedRatioDenom.tag(OptionTag::SATURATION);

    _theorySplitQueueCutoffs = StringOptionValue("theory_split_queue_cutoffs", "thsqc", "0,32,80");
    _theorySplitQueueCutoffs.description = "The cutoff-values for the split-queues (the cutoff value for the last queue has to be omitted, as it is always infinity). Any split-queue contains all clauses which are assigned a feature-value less or equal to the cutoff-value of the queue. If no custom value for this option is set, the implementation will use cutoffs 0,4*d,10*d,infinity (where d denotes the theory-split-queue-expected-ratio-denominator).";
    _lookup.insert(&_theorySplitQueueCutoffs);
    _theorySplitQueueCutoffs.reliesOn(_useTheorySplitQueues.is(equal(true)));
    _theorySplitQueueCutoffs.tag(OptionTag::SATURATION);
    _theorySplitQueueCutoffs.setExperimental();

    _theorySplitQueueRatios = StringOptionValue("theory_split_queue_ratios", "thsqr", "20,10,10,1");
    _theorySplitQueueRatios.description = "The ratios for picking clauses from the split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.";
    _lookup.insert(&_theorySplitQueueRatios);
    _theorySplitQueueRatios.reliesOn(_useTheorySplitQueues.is(equal(true)));
    _theorySplitQueueRatios.tag(OptionTag::SATURATION);
    _theorySplitQueueRatios.setExperimental();

    _theorySplitQueueLayeredArrangement = BoolOptionValue("theory_split_queue_layered_arrangement","thsql",true);
    _theorySplitQueueLayeredArrangement.description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.";
    _lookup.insert(&_theorySplitQueueLayeredArrangement);
    _theorySplitQueueLayeredArrangement.reliesOn(_useTheorySplitQueues.is(equal(true)));
    _theorySplitQueueLayeredArrangement.tag(OptionTag::SATURATION);
    _theorySplitQueueLayeredArrangement.setExperimental();

    _useAvatarSplitQueues = BoolOptionValue("avatar_split_queue","avsq",false);
    _useAvatarSplitQueues.description = "Turn on experiments: clause selection with multiple queues containing different clauses (split by amount of avatar-split-set-size)";
    _lookup.insert(&_useAvatarSplitQueues);
    _useAvatarSplitQueues.tag(OptionTag::AVATAR);
    _avatarSplitQueueCutoffs.reliesOn(_splitting.is(equal(true)));

    _avatarSplitQueueCutoffs = StringOptionValue("avatar_split_queue_cutoffs", "avsqc", "0");
    _avatarSplitQueueCutoffs.description = "The cutoff-values for the avatar-split-queues (the cutoff value for the last queue is omitted, since it has to be infinity).";
    _lookup.insert(&_avatarSplitQueueCutoffs);
    _avatarSplitQueueCutoffs.reliesOn(_useAvatarSplitQueues.is(equal(true)));
    _avatarSplitQueueCutoffs.tag(OptionTag::AVATAR);
    _avatarSplitQueueCutoffs.setExperimental();

    _avatarSplitQueueRatios = StringOptionValue("avatar_split_queue_ratios", "avsqr", "1,2");
    _avatarSplitQueueRatios.description = "The ratios for picking clauses from the split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.";
    _lookup.insert(&_avatarSplitQueueRatios);
    _avatarSplitQueueRatios.reliesOn(_useAvatarSplitQueues.is(equal(true)));
    _avatarSplitQueueRatios.tag(OptionTag::AVATAR);
    _avatarSplitQueueRatios.setExperimental();

    _avatarSplitQueueLayeredArrangement = BoolOptionValue("avatar_split_queue_layered_arrangement","avsql",false);
    _avatarSplitQueueLayeredArrangement.description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.";
    _lookup.insert(&_avatarSplitQueueLayeredArrangement);
    _avatarSplitQueueLayeredArrangement.reliesOn(_useAvatarSplitQueues.is(equal(true)));
    _avatarSplitQueueLayeredArrangement.tag(OptionTag::AVATAR);
    _avatarSplitQueueLayeredArrangement.setExperimental();

    _useSineLevelSplitQueues = BoolOptionValue("sine_level_split_queue","slsq",false);
    _useSineLevelSplitQueues.description = "Turn on experiments: clause selection with multiple queues containing different clauses (split by sine-level of clause)";
    _lookup.insert(&_useSineLevelSplitQueues);
    _useSineLevelSplitQueues.tag(OptionTag::SATURATION);

    _sineLevelSplitQueueCutoffs = StringOptionValue("sine_level_split_queue_cutoffs", "slsqc", "0");
    _sineLevelSplitQueueCutoffs.description = "The cutoff-values for the sine-level-split-queues (the cutoff value for the last queue is omitted, since it has to be infinity).";
    _lookup.insert(&_sineLevelSplitQueueCutoffs);
    _sineLevelSplitQueueCutoffs.reliesOn(_useSineLevelSplitQueues.is(equal(true)));
    _sineLevelSplitQueueCutoffs.tag(OptionTag::SATURATION);
    _sineLevelSplitQueueCutoffs.setExperimental();

    _sineLevelSplitQueueRatios = StringOptionValue("sine_level_split_queue_ratios", "slsqr", "1,3");
    _sineLevelSplitQueueRatios.description = "The ratios for picking clauses from the sine-level-split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.";
    _lookup.insert(&_sineLevelSplitQueueRatios);
    _sineLevelSplitQueueRatios.reliesOn(_useSineLevelSplitQueues.is(equal(true)));
    _sineLevelSplitQueueRatios.tag(OptionTag::SATURATION);
    _sineLevelSplitQueueRatios.setExperimental();

    _sineLevelSplitQueueLayeredArrangement = BoolOptionValue("sine_level_split_queue_layered_arrangement","slsql",true);
    _sineLevelSplitQueueLayeredArrangement.description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.";
    _lookup.insert(&_sineLevelSplitQueueLayeredArrangement);
    _sineLevelSplitQueueLayeredArrangement.reliesOn(_useSineLevelSplitQueues.is(equal(true)));
    _sineLevelSplitQueueLayeredArrangement.tag(OptionTag::SATURATION);
    _sineLevelSplitQueueLayeredArrangement.setExperimental();

	    _literalMaximalityAftercheck = BoolOptionValue("literal_maximality_aftercheck","lma",false);
	    _lookup.insert(&_literalMaximalityAftercheck);
	    _literalMaximalityAftercheck.tag(OptionTag::SATURATION);
	    _literalMaximalityAftercheck.setExperimental();

      _lrsFirstTimeCheck = IntOptionValue("lrs_first_time_check","",5);
      _lrsFirstTimeCheck.description=
      "Percentage of time limit at which the LRS algorithm will for the first time estimate the number of reachable clauses.";
      _lookup.insert(&_lrsFirstTimeCheck);
      _lrsFirstTimeCheck.tag(OptionTag::LRS);
      _lrsFirstTimeCheck.addConstraint(greaterThanEq(0));
      _lrsFirstTimeCheck.addConstraint(lessThan(100));

      _lrsWeightLimitOnly = BoolOptionValue("lrs_weight_limit_only","lwlo",false);
      _lrsWeightLimitOnly.description=
      "If off, the lrs sets both age and weight limit according to clause reachability, otherwise it sets the age limit to 0 and only the weight limit reflects reachable clauses";
      _lookup.insert(&_lrsWeightLimitOnly);
      _lrsWeightLimitOnly.tag(OptionTag::LRS);

      _simulatedTimeLimit = TimeLimitOptionValue("simulated_time_limit","stl",0);
      _simulatedTimeLimit.description=
      "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)";
      _lookup.insert(&_simulatedTimeLimit);
      _simulatedTimeLimit.tag(OptionTag::LRS);


  //*********************** Inferences  ***********************

#if VZ3

           _theoryInstAndSimp = ChoiceOptionValue<TheoryInstSimp>("theory_instantiation","thi",
                                                TheoryInstSimp::OFF,{"off","all","strong","overlap","full","new"});
           _theoryInstAndSimp.description = ""; 
           _theoryInstAndSimp.tag(OptionTag::INFERENCES);
           _lookup.insert(&_theoryInstAndSimp);
           _theoryInstAndSimp.setExperimental();
#endif
           _unificationWithAbstraction = ChoiceOptionValue<UnificationWithAbstraction>("unification_with_abstraction","uwa",
                                             UnificationWithAbstraction::OFF,
                                             {"off","interpreted_only","one_side_interpreted","one_side_constant","all","ground","fixed"});
           _unificationWithAbstraction.description="";
           _unificationWithAbstraction.tag(OptionTag::INFERENCES);
           _lookup.insert(&_unificationWithAbstraction);
           _unificationWithAbstraction.setExperimental();

           _useACeval = BoolOptionValue("use_ac_eval","uace",true);
           _useACeval.description="";
           _useACeval.tag(OptionTag::INFERENCES);
           _lookup.insert(&_useACeval);
           _useACeval.setExperimental();

            _induction = ChoiceOptionValue<Induction>("induction","ind",Induction::NONE,
                                {"none","struct","math","both"});
            _induction.description = "Apply structural and/or mathematical induction on datatypes and integers";
            _induction.tag(OptionTag::INFERENCES);
            _lookup.insert(&_induction);
            //_induction.setRandomChoices
            _induction.setExperimental();

            _structInduction = ChoiceOptionValue<StructuralInductionKind>("structural_induction_kind","sik",
                                 StructuralInductionKind::ONE,{"one","two","three","all"});
            _structInduction.description="";
            _structInduction.tag(OptionTag::INFERENCES);
            _structInduction.reliesOn(_induction.is(equal(Induction::STRUCTURAL))->Or<StructuralInductionKind>(_induction.is(equal(Induction::BOTH))));
            _lookup.insert(&_structInduction);
            _structInduction.setExperimental();

            _mathInduction = ChoiceOptionValue<MathInductionKind>("math_induction_kind","mik",
                                 MathInductionKind::ONE,{"one","two","all"});
            _mathInduction.description="";
            _mathInduction.tag(OptionTag::INFERENCES);
            _mathInduction.setExperimental();
            _mathInduction.reliesOn(_induction.is(equal(Induction::MATHEMATICAL))->Or<MathInductionKind>(_induction.is(equal(Induction::BOTH))));
            //_lookup.insert(&_mathInduction);

            _inductionChoice = ChoiceOptionValue<InductionChoice>("induction_choice","indc",InductionChoice::ALL,
                                {"all","goal","goal_plus"});
            _inductionChoice.description="Where to apply induction. Goal only applies to constants in goal, goal_plus"
                                         " extends this with skolem constants introduced by induction. Consider using" 
                                         " guess_the_goal for problems in SMTLIB as they do not come with a conjecture";
            _inductionChoice.tag(OptionTag::INFERENCES);
            _lookup.insert(&_inductionChoice);
            _inductionChoice.setExperimental();
            _inductionChoice.reliesOn(_induction.is(notEqual(Induction::NONE)));
            //_inductionChoice.addHardConstraint(If(equal(InductionChoice::GOAL)->Or(equal(InductionChoice::GOAL_PLUS))).then(
            //  _inputSyntax.is(equal(InputSyntax::TPTP))->Or<InductionChoice>(_guessTheGoal.is(equal(true)))));


            _maxInductionDepth = UnsignedOptionValue("induction_max_depth","indmd",0);
            _maxInductionDepth.description = "Set maximum depth of induction where 0 means no max.";
            _maxInductionDepth.setExperimental();
            _maxInductionDepth.tag(OptionTag::INFERENCES);
            _maxInductionDepth.reliesOn(_induction.is(notEqual(Induction::NONE)));
            _maxInductionDepth.addHardConstraint(lessThan(33u));
            _lookup.insert(&_maxInductionDepth);

            _inductionNegOnly = BoolOptionValue("induction_neg_only","indn",true);
            _inductionNegOnly.description = "Only apply induction to negative literals";
            _inductionNegOnly.setExperimental();
            _inductionNegOnly.tag(OptionTag::INFERENCES);
            _inductionNegOnly.reliesOn(_induction.is(notEqual(Induction::NONE)));
            _lookup.insert(&_inductionNegOnly);

            _inductionUnitOnly = BoolOptionValue("induction_unit_only","indu",true);
            _inductionUnitOnly.description = "Only apply induction to unit clauses";
            _inductionUnitOnly.setExperimental();
            _inductionUnitOnly.tag(OptionTag::INFERENCES);
            _inductionUnitOnly.reliesOn(_induction.is(notEqual(Induction::NONE)));
            _lookup.insert(&_inductionUnitOnly);

            _inductionGen = BoolOptionValue("induction_gen","indgen",false);
            _inductionGen.description = "Apply induction with generalization (on both all & selected occurrences)";
            _inductionGen.setExperimental();
            _inductionGen.tag(OptionTag::INFERENCES);
            _inductionGen.reliesOn(_induction.is(notEqual(Induction::NONE)));
            _lookup.insert(&_inductionGen);

            _maxInductionGenSubsetSize = UnsignedOptionValue("max_induction_gen_subset_size","indgenss",3);
            _maxInductionGenSubsetSize.description = "Set maximum number of occurrences of the induction term to be"
                                                      " generalized, where 0 means no max. (Regular induction will"
                                                      " be applied without this restriction.)";
            _maxInductionGenSubsetSize.setExperimental();
            _maxInductionGenSubsetSize.tag(OptionTag::INFERENCES);
            _maxInductionGenSubsetSize.reliesOn(_inductionGen.is(equal(true)));
            _maxInductionGenSubsetSize.addHardConstraint(lessThan(10u));
            _lookup.insert(&_maxInductionGenSubsetSize);

	    _instantiation = ChoiceOptionValue<Instantiation>("instantiation","inst",Instantiation::OFF,{"off","on"});
	    _instantiation.description = "Heuristically instantiate variables";
	    _instantiation.tag(OptionTag::INFERENCES);
	    _lookup.insert(&_instantiation);
	    _instantiation.setRandomChoices({"off","on"}); // Turn this on rarely
	    _instantiation.setExperimental();

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
	    _backwardDemodulation.addProblemConstraint(hasEquality());
	    _backwardDemodulation.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<Demodulation>(_instGenWithResolution.is(equal(true))));
	    _backwardDemodulation.setRandomChoices({"all","off"});

	    _backwardSubsumption = ChoiceOptionValue<Subsumption>("backward_subsumption","bs",
								  Subsumption::OFF,{"off","on","unit_only"});
	    _backwardSubsumption.description=
		     "Perform subsumption deletion of kept clauses by newly derived clauses. Unit_only means that the subsumption will be performed only by unit clauses";
	    _lookup.insert(&_backwardSubsumption);
	    _backwardSubsumption.tag(OptionTag::INFERENCES);
	    _backwardSubsumption.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<Subsumption>(_instGenWithResolution.is(equal(true))));
	    _backwardSubsumption.setRandomChoices({"on","off"});

	    _backwardSubsumptionResolution = ChoiceOptionValue<Subsumption>("backward_subsumption_resolution","bsr",
									    Subsumption::OFF,{"off","on","unit_only"});
	    _backwardSubsumptionResolution.description=
		     "Perform subsumption resolution on kept clauses using newly derived clauses. Unit_only means that the subsumption resolution will be performed only by unit clauses";
	    _lookup.insert(&_backwardSubsumptionResolution);
	    _backwardSubsumptionResolution.tag(OptionTag::INFERENCES);
	    _backwardSubsumptionResolution.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<Subsumption>(_instGenWithResolution.is(equal(true))));
	    _backwardSubsumptionResolution.setRandomChoices({"on","off"});

            _backwardSubsumptionDemodulation = BoolOptionValue("backward_subsumption_demodulation", "bsd", false);
            _backwardSubsumptionDemodulation.description = "Perform backward subsumption demodulation.";
            _lookup.insert(&_backwardSubsumptionDemodulation);
            _backwardSubsumptionDemodulation.tag(OptionTag::INFERENCES);
            _backwardSubsumptionDemodulation.addProblemConstraint(hasEquality());
            _backwardSubsumptionDemodulation.setRandomChoices({"on","off"});

            _backwardSubsumptionDemodulationMaxMatches = UnsignedOptionValue("backward_subsumption_demodulation_max_matches", "bsdmm", 0);
            _backwardSubsumptionDemodulationMaxMatches.description = "Maximum number of multi-literal matches to consider in backward subsumption demodulation. 0 means to try all matches (until first success).";
            _lookup.insert(&_backwardSubsumptionDemodulationMaxMatches);
            _backwardSubsumptionDemodulationMaxMatches.tag(OptionTag::INFERENCES);
            _backwardSubsumptionDemodulationMaxMatches.setRandomChoices({"0", "1", "3"});
            _backwardSubsumptionDemodulationMaxMatches.setExperimental();

	    _binaryResolution = BoolOptionValue("binary_resolution","br",true);
	    _binaryResolution.description=
		  "Standard binary resolution i.e.\n"
		      "C \\/ t     D \\/ s\n"
		      "---------------------\n"
		      "(C \\/ D)θ\n"
		      "where θ = mgu(t,-s) and t selected";
	    _lookup.insert(&_binaryResolution);
	    _binaryResolution.tag(OptionTag::INFERENCES);
	    // If urr is off then binary resolution should be on
	    _binaryResolution.addConstraint(
	      If(equal(false)).then(_unitResultingResolution.is(notEqual(URResolution::OFF))));
	    _binaryResolution.setRandomChoices(And(isRandSat(),saNotInstGen(),Or(hasEquality(),isBfnt(),hasCat(Property::HNE))),{"on"});
	    _binaryResolution.setRandomChoices({"on","off"});


	    _condensation = ChoiceOptionValue<Condensation>("condensation","cond",Condensation::OFF,{"fast","off","on"});
	    _condensation.description=
		     "Perform condensation. If 'fast' is specified, we only perform condensations that are easy to check for.";
	    _lookup.insert(&_condensation);
	    _condensation.tag(OptionTag::INFERENCES);
	    _condensation.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<Condensation>(_instGenWithResolution.is(equal(true))));
	    _condensation.setRandomChoices({"on","off","fast"});

	    _demodulationRedundancyCheck = BoolOptionValue("demodulation_redundancy_check","drc",true);
	    _demodulationRedundancyCheck.description=
		     "Avoids the following cases of backward and forward demodulation, as they do not preserve completeness:\n"
		     "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n"

		     "--------------------- \t ---------------------\n"
		     "t = t1 \\/ C \t\t t != t1 \\/ C\n"
		     "where t > t1 and s = t > C (RHS replaced)";
	    _lookup.insert(&_demodulationRedundancyCheck);
	    _demodulationRedundancyCheck.tag(OptionTag::INFERENCES);
	    _demodulationRedundancyCheck.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<bool>(_instGenWithResolution.is(equal(true))));
	    _demodulationRedundancyCheck.addProblemConstraint(hasEquality());
	    _demodulationRedundancyCheck.setRandomChoices({"on","off"});

	    
	    _extensionalityAllowPosEq = BoolOptionValue( "extensionality_allow_pos_eq","",false);
	    _extensionalityAllowPosEq.description="If extensionality resolution equals filter, this dictates"
	      " whether we allow other positive equalities when recognising extensionality clauses";
	    _lookup.insert(&_extensionalityAllowPosEq);
	    _extensionalityAllowPosEq.tag(OptionTag::INFERENCES);
	    _extensionalityAllowPosEq.reliesOn(_extensionalityResolution.is(equal(ExtensionalityResolution::FILTER)));
	    _extensionalityAllowPosEq.setRandomChoices({"on","off","off"}); // Prefer off
	    
	    _extensionalityMaxLength = UnsignedOptionValue("extensionality_max_length","",0);
	    _extensionalityMaxLength.description="Sets the maximum length (number of literals) an extensionality"
	      " clause can have when doing recognition for extensionality resolution. If zero there is no maximum.";
	    _lookup.insert(&_extensionalityMaxLength);
	    _extensionalityMaxLength.tag(OptionTag::INFERENCES);
	    // 0 means infinity, so it is intentionally not if (unsignedValue < 2).
	    _extensionalityMaxLength.addConstraint(notEqual(1u));
	    _extensionalityMaxLength.reliesOn(_extensionalityResolution.is(notEqual(ExtensionalityResolution::OFF)));
	    //TODO does this depend on anything?
	    _extensionalityMaxLength.setRandomChoices({"0","0","0","2","3"}); // TODO what are good values?
	    
	    _extensionalityResolution = ChoiceOptionValue<ExtensionalityResolution>("extensionality_resolution","er",
										    ExtensionalityResolution::OFF,{"filter","known","tagged","off"});
	    _extensionalityResolution.description=
	      "Turns on the following inference rule:\n"
	      "  x=y \\/ C    s != t \\/ D\n"
	      "  -----------------------\n"
	      "  C{x → s, y → t} \\/ D\n"
	      "Where s!=t is selected in s!=t \\/D and x=y \\/ C is a recognised as an extensionality clause - how clauses are recognised depends on the value of this option.\n"
	      "If filter we attempt to recognise all extensionality clauses i.e. those that have exactly one X=Y, no inequality of the same sort as X-Y (and optionally no equality except X=Y, see extensionality_allow_pos_eq).\n" 
	      "If known we only recognise a known set of extensionality clauses. At the moment this includes the standard and subset-based formulations of the set extensionality axiom, as well as the array extensionality axiom.\n"
	      "If tagged we only use formulas tagged as extensionality clauses.";
	    _lookup.insert(&_extensionalityResolution);
	    _extensionalityResolution.tag(OptionTag::INFERENCES);
	    // Captures that if ExtensionalityResolution is not off then inequality splitting must be 0
	    _extensionalityResolution.reliesOn(_inequalitySplitting.is(equal(0)));
	    _extensionalityResolution.setRandomChoices({"filter","known","off","off"});

	    _FOOLParamodulation = BoolOptionValue("fool_paramodulation","foolp",false);
	    _FOOLParamodulation.description=
	      "Turns on the following inference rule:\n"
	      "        C[s]\n"
	      "--------------------,\n"
	      "C[true] \\/ s = false\n"
	      "where s is a boolean term that is not a variable, true or false, C[true] is "
	      "the C clause with s substituted by true. This rule is needed for effecient "
	      "treatment of boolean terms.";
	    _lookup.insert(&_FOOLParamodulation);
	    _FOOLParamodulation.tag(OptionTag::INFERENCES);

            _termAlgebraInferences = BoolOptionValue("term_algebra_rules","tar",true);
            _termAlgebraInferences.description=
              "Activates some rules that improve reasoning with term algebras (such as algebraic datatypes in SMT-LIB):\n"
              "If the problem does not contain any term algebra symbols, activating this options has no effect\n"
              "- distinctness rule:\n"
              "f(...) = g(...) \\/ A\n"
              "--------------------\n"
              "          A         \n"
              "where f and g are distinct term algebra constructors\n"
              "- distinctness tautology deletion: clauses of the form f(...) ~= g(...) \\/ A are deleted\n"
              "- injectivity rule:\n"
              "f(s1 ... sn) = f(t1 ... tn) \\/ A\n"
              "--------------------------------\n"
              "         s1 = t1 \\/ A\n"
              "               ...\n"
              "         sn = tn \\/ A";
            _lookup.insert(&_termAlgebraInferences);
            _termAlgebraInferences.tag(OptionTag::INFERENCES);

            _termAlgebraCyclicityCheck = ChoiceOptionValue<TACyclicityCheck>("term_algebra_acyclicity","tac",
                                                                             TACyclicityCheck::OFF,{"off","axiom","rule","light"});
            _termAlgebraCyclicityCheck.description=
              "Activates the cyclicity rule for term algebras (such as algebraic datatypes in SMT-LIB):\n"
              "- off : the cyclicity rule is not enforced (this is sound but incomplete)\n"
              "- axiom : the cyclicity rule is axiomatized with a transitive predicate describing the subterm relation over terms\n"
              "- rule : the cyclicity rule is enforced by a specific hyper-resolution rule\n"
              "- light : the cyclicity rule is enforced by rule generating disequality between a term and its known subterms";
            _lookup.insert(&_termAlgebraCyclicityCheck);
            _termAlgebraCyclicityCheck.tag(OptionTag::INFERENCES);

	    _forwardDemodulation = ChoiceOptionValue<Demodulation>("forward_demodulation","fd",Demodulation::ALL,{"all","off","preordered"});
	    _forwardDemodulation.description=
	    "Oriented rewriting of newly derived clauses by kept unit equalities\n"
	    "s = t     L[sθ] \\/ C\n"
	    "---------------------  where sθ > tθ\n"
	    " L[tθ] \\/ C\n"
	    "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.";
	    _lookup.insert(&_forwardDemodulation);
	    _forwardDemodulation.tag(OptionTag::INFERENCES);
	    _forwardDemodulation.setRandomChoices({"all","all","all","off","preordered"});
    
    _forwardLiteralRewriting = BoolOptionValue("forward_literal_rewriting","flr",false);
    _forwardLiteralRewriting.description="Perform forward literal rewriting.";
    _lookup.insert(&_forwardLiteralRewriting);
    _forwardLiteralRewriting.tag(OptionTag::INFERENCES);
    _forwardLiteralRewriting.addProblemConstraint(hasNonUnits());
    _forwardLiteralRewriting.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<bool>(_instGenWithResolution.is(equal(true))));
    _forwardLiteralRewriting.setRandomChoices({"on","off"});

    _forwardSubsumption = BoolOptionValue("forward_subsumption","fs",true);
    _forwardSubsumption.description="Perform forward subsumption deletion.";
    _lookup.insert(&_forwardSubsumption);
    _forwardSubsumption.tag(OptionTag::INFERENCES);
    _forwardSubsumption.setRandomChoices({"on","on","on","on","on","on","on","on","on","off"}); // turn this off rarely

    _forwardSubsumptionResolution = BoolOptionValue("forward_subsumption_resolution","fsr",true);
    _forwardSubsumptionResolution.description="Perform forward subsumption resolution.";
    _lookup.insert(&_forwardSubsumptionResolution);
    _forwardSubsumptionResolution.tag(OptionTag::INFERENCES);
    _forwardSubsumptionResolution.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<bool>(_instGenWithResolution.is(equal(true))));
    _forwardSubsumptionResolution.setRandomChoices({"on","off"});

    _forwardSubsumptionDemodulation = BoolOptionValue("forward_subsumption_demodulation", "fsd", false);
    _forwardSubsumptionDemodulation.description = "Perform forward subsumption demodulation.";
    _lookup.insert(&_forwardSubsumptionDemodulation);
    _forwardSubsumptionDemodulation.tag(OptionTag::INFERENCES);
    _forwardSubsumptionDemodulation.addProblemConstraint(hasEquality());
    _forwardSubsumptionDemodulation.setRandomChoices({"off","on"});

    _forwardSubsumptionDemodulationMaxMatches = UnsignedOptionValue("forward_subsumption_demodulation_max_matches", "fsdmm", 0);
    _forwardSubsumptionDemodulationMaxMatches.description = "Maximum number of multi-literal matches to consider in forward subsumption demodulation. 0 means to try all matches (until first success).";
    _lookup.insert(&_forwardSubsumptionDemodulationMaxMatches);
    _forwardSubsumptionDemodulationMaxMatches.tag(OptionTag::INFERENCES);
    _forwardSubsumptionDemodulationMaxMatches.setRandomChoices({"0", "1", "3"});
    _forwardSubsumptionDemodulationMaxMatches.setExperimental();

    _hyperSuperposition = BoolOptionValue("hyper_superposition","",false);
    _hyperSuperposition.description=
    "Simplifying inference that attempts to do several rewritings at once if it will eliminate literals of the original clause (now we aim just for elimination by equality resolution)";
    _lookup.insert(&_hyperSuperposition);
    _hyperSuperposition.tag(OptionTag::INFERENCES);

    _simultaneousSuperposition = BoolOptionValue("simultaneous_superposition","sims",true);
    _simultaneousSuperposition.description="Rewrite the whole RHS clause during superposition, not just the target literal.";
    _lookup.insert(&_simultaneousSuperposition);
    _simultaneousSuperposition.tag(OptionTag::INFERENCES);
    _simultaneousSuperposition.setExperimental();

    _innerRewriting = BoolOptionValue("inner_rewriting","irw",false);
    _innerRewriting.description="C[t_1] | t1 != t2 ==> C[t_2] | t1 != t2 when t1>t2";
    _lookup.insert(&_innerRewriting);
    _innerRewriting.tag(OptionTag::INFERENCES);
    _innerRewriting.setExperimental();

    _equationalTautologyRemoval = BoolOptionValue("equational_tautology_removal","etr",false);
    _equationalTautologyRemoval.description="A reduction which uses CC to remove logically valid clauses.";
    _lookup.insert(&_equationalTautologyRemoval);
    _equationalTautologyRemoval.tag(OptionTag::INFERENCES);
    _equationalTautologyRemoval.setExperimental();

    _unitResultingResolution = ChoiceOptionValue<URResolution>("unit_resulting_resolution","urr",URResolution::OFF,{"ec_only","off","on"});
    _unitResultingResolution.description=
    "Uses unit resulting resolution only to derive empty clauses (may be useful for splitting)";
    _lookup.insert(&_unitResultingResolution);
    _unitResultingResolution.tag(OptionTag::INFERENCES);
    // Wrong, should instead suggest that urr is always used with inst_gen
    //_unitResultingResolution.reliesOn(
    //  _saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->And<URResolution,bool>(
    //    _instGenWithResolution.is(notEqual(true))));
    _unitResultingResolution.addProblemConstraint(hasPredicates());
    // If br has already been set off then this will be forced on, if br has not yet been set
    // then setting this to off will force br on
    _unitResultingResolution.setRandomChoices(And(isRandSat(),saNotInstGen(),Or(hasEquality(),isBfnt(),hasCat(Property::HNE))),{"on","off"});
    _unitResultingResolution.setRandomChoices(isRandSat(),{});
    _unitResultingResolution.setRandomChoices({"on","on","off"});


    _superpositionFromVariables = BoolOptionValue("superposition_from_variables","sfv",true);
    _superpositionFromVariables.description="Perform superposition from variables.";
    _lookup.insert(&_superpositionFromVariables);
    _superpositionFromVariables.tag(OptionTag::INFERENCES);
    _superpositionFromVariables.addProblemConstraint(hasEquality());
    _superpositionFromVariables.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN))->Or<bool>(_instGenWithResolution.is(equal(true))));
    _superpositionFromVariables.setRandomChoices({"on","off"});

//*********************** InstGen  ***********************

    _globalSubsumption = BoolOptionValue("global_subsumption","gs",false);
    _globalSubsumption.description="Perform global subsumption. Use a set of groundings of generated clauses G to replace C \\/ L by C if the grounding of C is implied by G. A SAT solver is used for ground reasoning.";
    _lookup.insert(&_globalSubsumption);
    _globalSubsumption.tag(OptionTag::INFERENCES);
    _globalSubsumption.addProblemConstraint(hasNonUnits());
    _globalSubsumption.setRandomChoices({"off","on"});

    _globalSubsumptionSatSolverPower = ChoiceOptionValue<GlobalSubsumptionSatSolverPower>("global_subsumption_sat_solver_power","gsssp",
          GlobalSubsumptionSatSolverPower::PROPAGATION_ONLY,{"propagation_only","full"});
    _globalSubsumptionSatSolverPower.description="";
    _lookup.insert(&_globalSubsumptionSatSolverPower);
    _globalSubsumptionSatSolverPower.tag(OptionTag::INFERENCES);
    _globalSubsumptionSatSolverPower.reliesOn(_globalSubsumption.is(equal(true)));
    _globalSubsumptionSatSolverPower.setRandomChoices({"propagation_only","full"});
    _globalSubsumptionSatSolverPower.setExperimental();

    _globalSubsumptionExplicitMinim = ChoiceOptionValue<GlobalSubsumptionExplicitMinim>("global_subsumption_explicit_minim","gsem",
        GlobalSubsumptionExplicitMinim::RANDOMIZED,{"off","on","randomized"});
    _globalSubsumptionSatSolverPower.description="Explicitly minimize the result of global sumsumption reduction.";
    _lookup.insert(&_globalSubsumptionExplicitMinim);
    _globalSubsumptionExplicitMinim.tag(OptionTag::INFERENCES);
    _globalSubsumptionExplicitMinim.reliesOn(_globalSubsumption.is(equal(true)));
    _globalSubsumptionExplicitMinim.setRandomChoices({"off","on","randomized"});
    _globalSubsumptionExplicitMinim.setExperimental();

    _globalSubsumptionAvatarAssumptions = ChoiceOptionValue<GlobalSubsumptionAvatarAssumptions>("global_subsumption_avatar_assumptions","gsaa",
        GlobalSubsumptionAvatarAssumptions::OFF,{"off","from_current","full_model"});
    _globalSubsumptionAvatarAssumptions.description="";
    _lookup.insert(&_globalSubsumptionAvatarAssumptions);
    _globalSubsumptionAvatarAssumptions.tag(OptionTag::INFERENCES);
    _globalSubsumptionAvatarAssumptions.reliesOn(_globalSubsumption.is(equal(true)));
    _globalSubsumptionAvatarAssumptions.reliesOn(_splitting.is(equal(true)));
    _globalSubsumptionAvatarAssumptions.setRandomChoices({"off","from_current","full_model"});
    _globalSubsumptionAvatarAssumptions.setExperimental();

    _instGenBigRestartRatio = FloatOptionValue("inst_gen_big_restart_ratio","igbrr",0.0);
    _instGenBigRestartRatio.description=
    "Determines how often a big restart (instance generation starts from input clauses) will be performed. Small restart means all clauses generated so far are processed again.";
    _lookup.insert(&_instGenBigRestartRatio);
    _instGenBigRestartRatio.tag(OptionTag::INST_GEN);
    _instGenBigRestartRatio.addConstraint(greaterThanEq(0.0f)->And(lessThanEq(1.0f)));
    // Captures that this is only non-default when saturationAlgorithm is instgen
    _instGenBigRestartRatio.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _instGenBigRestartRatio.setRandomChoices({"0.0","0.1","0.2","0.3","0.4","0.5","0.6","0.7","0.8","0.9","1.0"});

    _instGenPassiveReactivation = BoolOptionValue("inst_gen_passive_reactivation","igpr",false);
    _instGenPassiveReactivation.description="When the model describing the selection function changes some active clauses may become lazily deselected. If passive reaction is selected these clauses are added into the passive set before recomputing the next model, otherwise they are added back to active.";
    _lookup.insert(&_instGenPassiveReactivation);
    _instGenPassiveReactivation.tag(OptionTag::INST_GEN);
    _instGenPassiveReactivation.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));

    _instGenResolutionInstGenRatio = RatioOptionValue("inst_gen_resolution_ratio","igrr",1,1,'/');
    _instGenResolutionInstGenRatio.description=
    "Ratio of resolution and instantiation steps (applies only if inst_gen_with_resolution is on)";
    _lookup.insert(&_instGenResolutionInstGenRatio);
    _instGenResolutionInstGenRatio.tag(OptionTag::INST_GEN);
    _instGenResolutionInstGenRatio.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _instGenResolutionInstGenRatio.reliesOn(_instGenWithResolution.is(equal(true)));
    _instGenResolutionInstGenRatio.setRandomChoices({"128/1","64/1","32/1","16/1","8/1","4/1","2/1","1/1","1/2","1/4","1/8","1/16","1/32","1/64","1/128"});

    _instGenRestartPeriod = IntOptionValue("inst_gen_restart_period","igrp",1000);
    _instGenRestartPeriod.description="How many clauses are processed before restart. The size of the restart depends on inst_gen_big_restart_ratio.";
    _lookup.insert(&_instGenRestartPeriod);
    _instGenRestartPeriod.tag(OptionTag::INST_GEN);
    _instGenRestartPeriod.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _instGenRestartPeriod.setRandomChoices({"100","200","400","700","1000","1400","2000","4000"});

    _instGenRestartPeriodQuotient = FloatOptionValue("inst_gen_restart_period_quotient","igrpq",1.0);
    _instGenRestartPeriodQuotient.description="Restart period is multiplied by this number after each restart.";
    _lookup.insert(&_instGenRestartPeriodQuotient);
    _instGenRestartPeriodQuotient.tag(OptionTag::INST_GEN);
    _instGenRestartPeriodQuotient.addConstraint(greaterThanEq(1.0f));
    _instGenRestartPeriodQuotient.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _instGenRestartPeriodQuotient.setRandomChoices({"1.0","1.05","1.1","1.2","1.3","1.5","2.0"});

    _instGenSelection = SelectionOptionValue("inst_gen_selection","igs",0);
    _instGenSelection.description=
    "Selection function for InstGen. This is applied *after* model-based selection is applied. "
    "For consistency the value 1011 is used to denote look-ahead selection.";
    _instGenSelection.addHardConstraint(notEqual(11)); // Use 1011 for look-ahead in InstGen instead.
    _lookup.insert(&_instGenSelection);
    _instGenSelection.tag(OptionTag::INST_GEN);
    _instGenSelection.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));

    _instGenWithResolution = BoolOptionValue("inst_gen_with_resolution","igwr",false);
    _instGenWithResolution.description=
    "Performs instantiation together with resolution (global subsumption index is shared, also clauses generated by the resolution are added to the instance SAT problem)";
    _lookup.insert(&_instGenWithResolution);
    _instGenWithResolution.tag(OptionTag::INST_GEN);
    _instGenWithResolution.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _instGenWithResolution.setRandomChoices({"on","off"});

    _useHashingVariantIndex = BoolOptionValue("use_hashing_clause_variant_index","uhcvi",false);
    _useHashingVariantIndex.description= "Use clause variant index based on hashing for clause variant detection (affects inst_gen and avatar).";
    _lookup.insert(&_useHashingVariantIndex);
    _useHashingVariantIndex.tag(OptionTag::OTHER);
    _useHashingVariantIndex.setExperimental();
    _useHashingVariantIndex.setRandomChoices({"on","off"});

    /*
    _use_dm = BoolOptionValue("use_dismatching","dm",false);
    _use_dm.description="Use dismatching constraints.";
    // Dismatching constraints didn't work and are being discontinued ...
    // _lookup.insert(&_use_dm);
    _use_dm.tag(OptionTag::INST_GEN);
    //_use_dm.setExperimental();
    _use_dm.setRandomChoices({"on","off"});
    _use_dm.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    */

    _nicenessOption = ChoiceOptionValue<Niceness>("niceness_option","none",Niceness::NONE,{"average","none","sum","top"});
    _nicenessOption.description="";
    _lookup.insert(&_nicenessOption);
    _nicenessOption.tag(OptionTag::INST_GEN);
    _nicenessOption.setExperimental();
    _nicenessOption.reliesOn(_saturationAlgorithm.is(equal(SaturationAlgorithm::INST_GEN)));
    _nicenessOption.reliesOn(_satSolver.is(equal(SatSolver::VAMPIRE)));
    _nicenessOption.setRandomChoices({"none","none","none","none","none","average","sum","top"});

//*********************** AVATAR  ***********************

    _splitting = BoolOptionValue("avatar","av",true);
    _splitting.description="Use AVATAR splitting.";
    _lookup.insert(&_splitting);
    _splitting.tag(OptionTag::AVATAR);
    //_splitting.addProblemConstraint(hasNonUnits());
    _splitting.setRandomChoices({"on","off"}); //TODO change balance?

    _splitAtActivation = BoolOptionValue("split_at_activation","sac",false);
    _splitAtActivation.description="Split a clause when it is activated, default is to split when it is processed";
    _lookup.insert(&_splitAtActivation);
    _splitAtActivation.reliesOn(_splitting.is(equal(true)));
    _splitAtActivation.tag(OptionTag::AVATAR);
    _splitAtActivation.setRandomChoices({"on","off"});

    _splittingAddComplementary = ChoiceOptionValue<SplittingAddComplementary>("avatar_add_complementary","aac",
                                                                                SplittingAddComplementary::GROUND,{"ground","none"});
    _splittingAddComplementary.description="";
    _lookup.insert(&_splittingAddComplementary);
    _splittingAddComplementary.tag(OptionTag::AVATAR);
    _splittingAddComplementary.setExperimental();
    _splittingAddComplementary.reliesOn(_splitting.is(equal(true)));
    _splittingAddComplementary.setRandomChoices({"ground","none"});


    _splittingCongruenceClosure = ChoiceOptionValue<SplittingCongruenceClosure>("avatar_congruence_closure","acc",
                                                                                SplittingCongruenceClosure::OFF,{"model","off","on"});
    _splittingCongruenceClosure.description="Use a congruence closure decision procedure on top of the AVATAR SAT solver. This ensures that models produced by AVATAR satisfy the theory of uninterprted functions.";
    _lookup.insert(&_splittingCongruenceClosure);
    _splittingCongruenceClosure.tag(OptionTag::AVATAR);
    _splittingCongruenceClosure.reliesOn(_splitting.is(equal(true)));
#if VZ3
    _splittingCongruenceClosure.reliesOn(_satSolver.is(notEqual(SatSolver::Z3)));
#endif
    _splittingCongruenceClosure.addProblemConstraint(hasEquality());
    _splittingCongruenceClosure.setRandomChoices({"model","off","on"});
    _splittingCongruenceClosure.addHardConstraint(If(equal(SplittingCongruenceClosure::MODEL)).
                                                  then(_splittingMinimizeModel.is(notEqual(SplittingMinimizeModel::SCO))));
    
    _ccUnsatCores = ChoiceOptionValue<CCUnsatCores>("cc_unsat_cores","ccuc",CCUnsatCores::ALL,
                                                     {"first", "small_ones", "all"});
    _ccUnsatCores.description="";
    _lookup.insert(&_ccUnsatCores);
    _ccUnsatCores.tag(OptionTag::AVATAR);
    _ccUnsatCores.reliesOn(_splittingCongruenceClosure.is(notEqual(SplittingCongruenceClosure::OFF)));
    _ccUnsatCores.setRandomChoices({"first", "small_ones", "all"});
    _ccUnsatCores.setExperimental();

    _splittingLiteralPolarityAdvice = ChoiceOptionValue<SplittingLiteralPolarityAdvice>(
                                                "avatar_literal_polarity_advice","alpa",
                                                SplittingLiteralPolarityAdvice::NONE,
                                                {"false","true","none"});
    _splittingLiteralPolarityAdvice.description="Override SAT-solver's default polarity/phase setting for variables abstracting clause components.";
    _lookup.insert(&_splittingLiteralPolarityAdvice);
    _splittingLiteralPolarityAdvice.tag(OptionTag::AVATAR);
    _splittingLiteralPolarityAdvice.reliesOn(_splitting.is(equal(true)));
    _splittingLiteralPolarityAdvice.setExperimental();

    _splittingMinimizeModel = ChoiceOptionValue<SplittingMinimizeModel>("avatar_minimize_model","amm",
                                                                        SplittingMinimizeModel::ALL,{"off","sco","all"});
    
    _splittingMinimizeModel.description="Minimize the SAT-solver model by replacing concrete values with don't-cares"
                                        " provided <all> the sat clauses (or only the split clauses with <sco>) remain provably satisfied"
                                        " by the partial model.";
    _lookup.insert(&_splittingMinimizeModel);
    _splittingMinimizeModel.tag(OptionTag::AVATAR);
    //_splittingMinimizeModel.setExperimental();
    _splittingMinimizeModel.reliesOn(_splitting.is(equal(true)));
    _splittingMinimizeModel.setRandomChoices({"off","sco","all"});

    _splittingEagerRemoval = BoolOptionValue("avatar_eager_removal","aer",true);
    _splittingEagerRemoval.description="If a component was in the model and then becomes 'don't care' eagerly remove that component from the first-order solver. Note: only has any impact when smm is used.";
    _lookup.insert(&_splittingEagerRemoval);
    _splittingEagerRemoval.tag(OptionTag::AVATAR);
    //_splittingEagerRemoval.setExperimental();
    _splittingEagerRemoval.reliesOn(_splitting.is(equal(true)));
    // if minimize is off then makes no difference
    // if minimize is sco then we could have a conflict clause added infinitely often
    _splittingEagerRemoval.reliesOn(_splittingMinimizeModel.is(equal(SplittingMinimizeModel::ALL)));
    _splittingEagerRemoval.setRandomChoices({"on","off"});

    _splittingFastRestart = BoolOptionValue("avatar_fast_restart","afr",false);
    _splittingFastRestart.description="";
    _lookup.insert(&_splittingFastRestart);
    _splittingFastRestart.tag(OptionTag::AVATAR);
    _splittingFastRestart.setExperimental();
    _splittingFastRestart.reliesOn(_splitting.is(equal(true)));
    _splittingFastRestart.setRandomChoices({"on","off"});

    _splittingBufferedSolver = BoolOptionValue("avatar_buffered_solver","abs",false);
    _splittingBufferedSolver.description="Added buffering funcitonality to the SAT solver used in AVATAR.";
    _lookup.insert(&_splittingBufferedSolver);
    _splittingBufferedSolver.tag(OptionTag::AVATAR);
    _splittingBufferedSolver.setExperimental();
    _splittingBufferedSolver.reliesOn(_splitting.is(equal(true)));
    _splittingBufferedSolver.setRandomChoices({"on","off"});

    _splittingDeleteDeactivated = ChoiceOptionValue<SplittingDeleteDeactivated>("avatar_delete_deactivated","add",
                                                                        SplittingDeleteDeactivated::ON,{"on","large","off"});

    _splittingDeleteDeactivated.description="";
    _lookup.insert(&_splittingDeleteDeactivated);
    _splittingDeleteDeactivated.tag(OptionTag::AVATAR);
    _splittingDeleteDeactivated.setExperimental();
    _splittingDeleteDeactivated.reliesOn(_splitting.is(equal(true)));
    _splittingDeleteDeactivated.setRandomChoices({"on","large","off"});


    _splittingFlushPeriod = UnsignedOptionValue("avatar_flush_period","afp",0);
    _splittingFlushPeriod.description=
    "after given number of generated clauses without deriving an empty clause, the splitting component selection is shuffled. If equal to zero, shuffling is never performed.";
    _lookup.insert(&_splittingFlushPeriod);
    _splittingFlushPeriod.tag(OptionTag::AVATAR);
    _splittingFlushPeriod.setExperimental();
    _splittingFlushPeriod.reliesOn(_splitting.is(equal(true)));
    _splittingFlushPeriod.setRandomChoices({"0","1000","4000","10000","40000","100000"});

    _splittingFlushQuotient = FloatOptionValue("avatar_flush_quotient","afq",1.5);
    _splittingFlushQuotient.description=
    "after each flush, the avatar_flush_period is multiplied by the quotient";
    _lookup.insert(&_splittingFlushQuotient);
    _splittingFlushQuotient.tag(OptionTag::AVATAR);
    _splittingFlushQuotient.setExperimental();
    _splittingFlushQuotient.addConstraint(greaterThanEq(1.0f));
    _splittingFlushQuotient.reliesOn(_splitting.is(equal(true)));
    _splittingFlushQuotient.setRandomChoices({"1.0","1.1","1.2","1.4","2.0"});

    _splittingNonsplittableComponents = ChoiceOptionValue<SplittingNonsplittableComponents>("avatar_nonsplittable_components","anc",
                                                                                              SplittingNonsplittableComponents::KNOWN,
                                                                                              {"all","all_dependent","known","none"});
    _splittingNonsplittableComponents.description=
    "Decide what to do with a nonsplittable component:\n"
    "  -known: SAT clauses will be learnt from non-splittable clauses that have corresponding components (if there is a component C with name SAT l, clause C | {l1,..ln} will give SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original FO clause C | {l1,..ln} and let the component selection update model, possibly adding the component clause C | {l}.\n"
    "  -all: like known, except when we see a non-splittable clause that doesn't have a name, we introduce the name for it.\n"
    "  -all_dependent: like all, but we don't introduce names for non-splittable clauses that don't depend on any components";
    _lookup.insert(&_splittingNonsplittableComponents);
    _splittingNonsplittableComponents.tag(OptionTag::AVATAR);
    //_splittingNonsplittableComponents.setExperimental();
    _splittingNonsplittableComponents.reliesOn(_splitting.is(equal(true)));
    _splittingNonsplittableComponents.setRandomChoices({"all","all_dependent","known","none"});


    _nonliteralsInClauseWeight = BoolOptionValue("nonliterals_in_clause_weight","nicw",false);
    _nonliteralsInClauseWeight.description=
    "Non-literal parts of clauses (such as its split history) will also contribute to the weight";
    _lookup.insert(&_nonliteralsInClauseWeight);
    _nonliteralsInClauseWeight.tag(OptionTag::AVATAR);
    _nonliteralsInClauseWeight.reliesOn(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::INST_GEN)));
    _nonliteralsInClauseWeight.reliesOn(_splitting.is(notEqual(false)));
    _nonliteralsInClauseWeight.addProblemConstraint(hasNonUnits());
    _nonliteralsInClauseWeight.setRandomChoices({"on","off"});

//*********************** SAT solver (used in various places)  ***********************

    _satClauseActivityDecay = FloatOptionValue("sat_clause_activity_decay","",1.001f);
    _satClauseActivityDecay.description="";
    _lookup.insert(&_satClauseActivityDecay);
    _satClauseActivityDecay.tag(OptionTag::SAT);
    _satClauseActivityDecay.addConstraint(greaterThan(1.0f));
    _satClauseActivityDecay.setExperimental();

    _satClauseDisposer = ChoiceOptionValue<SatClauseDisposer>("sat_clause_disposer","",SatClauseDisposer::MINISAT,
                                                              {"growing","minisat"});
    _satClauseDisposer.description="";
    _lookup.insert(&_satClauseDisposer);
    _satClauseDisposer.tag(OptionTag::SAT);
    _satClauseDisposer.setExperimental();

    _satLearntMinimization = BoolOptionValue("sat_learnt_minimization","",true);
    _satLearntMinimization.description="";
    _lookup.insert(&_satLearntMinimization);
    _satLearntMinimization.tag(OptionTag::SAT);
    _satLearntMinimization.setExperimental();

    _satLearntSubsumptionResolution = BoolOptionValue("sat_learnt_subsumption_resolution","",true);
    _satLearntSubsumptionResolution.description="";
    _lookup.insert(&_satLearntSubsumptionResolution);
    _satLearntSubsumptionResolution.tag(OptionTag::SAT);
    _satLearntSubsumptionResolution.setExperimental();

    _satRestartFixedCount = IntOptionValue("sat_restart_fixed_count","",16000);
    _satRestartFixedCount.description="";
    _lookup.insert(&_satRestartFixedCount);
    _satRestartFixedCount.tag(OptionTag::SAT);
    _satRestartFixedCount.setExperimental();

    _satRestartGeometricIncrease = FloatOptionValue("sat_restart_geometric_increase","",1.1);
    _satRestartGeometricIncrease.description="";
    _lookup.insert(&_satRestartGeometricIncrease);
    _satRestartGeometricIncrease.tag(OptionTag::SAT);
    _satRestartGeometricIncrease.addConstraint(greaterThan(1.0f));
    _satRestartGeometricIncrease.setExperimental();

    _satRestartGeometricInit = IntOptionValue("sat_restart_geometric_init","",32);
    _satRestartGeometricInit.description="";
    _lookup.insert(&_satRestartGeometricInit);
    _satRestartGeometricInit.tag(OptionTag::SAT);
    _satRestartGeometricInit.setExperimental();

    _satRestartLubyFactor = IntOptionValue("sat_restart_luby_factor","",100);
    _satRestartLubyFactor.description="";
    _lookup.insert(&_satRestartLubyFactor);
    _satRestartLubyFactor.tag(OptionTag::SAT);
    _satRestartLubyFactor.setExperimental();

    _satRestartMinisatIncrease = FloatOptionValue("sat_restart_minisat_increase","",1.1);
    _satRestartMinisatIncrease.description="";
    _lookup.insert(&_satRestartMinisatIncrease);
    _satRestartMinisatIncrease.tag(OptionTag::SAT);
    _satRestartMinisatIncrease.addConstraint(greaterThan(1.0f));
    _satRestartMinisatIncrease.setExperimental();

    _satRestartMinisatInit = IntOptionValue("sat_restart_minisat_init","",100);
    _satRestartMinisatInit.description="";
    _lookup.insert(&_satRestartMinisatInit);
    _satRestartMinisatInit.tag(OptionTag::SAT);
    _satRestartMinisatInit.setExperimental();

    _satRestartStrategy = ChoiceOptionValue<SatRestartStrategy>("sat_restart_strategy","",SatRestartStrategy::LUBY,
                                                                {"fixed","geometric","luby","minisat"});
    _satRestartStrategy.description="";
    _lookup.insert(&_satRestartStrategy);
    _satRestartStrategy.tag(OptionTag::SAT);
    _satRestartStrategy.setExperimental();

    _satSolver = ChoiceOptionValue<SatSolver>("sat_solver","sas",SatSolver::MINISAT,
#if VZ3
            {"minisat","vampire","z3"});
#else
    {"minisat","vampire"});
#endif
    _satSolver.description=
    "Select the SAT solver to be used throughout the solver. This will be used in AVATAR (for splitting) when the saturation algorithm is discount,lrs or otter and in instance generation for selection and global subsumption.";
    _lookup.insert(&_satSolver);
    _satSolver.tag(OptionTag::SAT);
    _satSolver.setRandomChoices(
#if VZ3
            {"minisat","vampire","z3"});
#else
            {"minisat","vampire"});
#endif

#if VZ3
    _satFallbackForSMT = BoolOptionValue("sat_fallback_for_smt","sffsmt",false);
    _satFallbackForSMT.description="If using z3 run a sat solver alongside to use if the smt"
       " solver returns unknown at any point";
    _lookup.insert(&_satFallbackForSMT);
    _satFallbackForSMT.tag(OptionTag::SAT);
    _satFallbackForSMT.reliesOn(_satSolver.is(equal(SatSolver::Z3)));

    _z3UnsatCores = BoolOptionValue("z3_unsat_core","z3uc",false);
    _z3UnsatCores.description=""; 
    _lookup.insert(&_z3UnsatCores);
    _z3UnsatCores.setExperimental();
    _z3UnsatCores.tag(OptionTag::SAT);
#endif

    _satVarActivityDecay = FloatOptionValue("sat_var_activity_decay","",1.05f);
    _satVarActivityDecay.description="";
    _lookup.insert(&_satVarActivityDecay);
    _satVarActivityDecay.tag(OptionTag::SAT);
    _satVarActivityDecay.addConstraint(greaterThan(1.0f));
    _satVarActivityDecay.setExperimental();

    _satVarSelector = ChoiceOptionValue<SatVarSelector>("sat_var_selector","svs",SatVarSelector::ACTIVE,
                                                        {"active","niceness","recently_learnt"});
    _satVarSelector.description="";
    _lookup.insert(&_satVarSelector);
    _satVarSelector.tag(OptionTag::SAT);
    _satVarSelector.setExperimental();

    //*************************************************************
    //*********************** which mode or tag?  ************************
    //*************************************************************
    
    _bfnt = BoolOptionValue("bfnt","bfnt",false);
    _bfnt.description="";
    _lookup.insert(&_bfnt);
    _bfnt.tag(OptionTag::SATURATION);
    // This is checked in checkGlobal
    //_bfnt.addConstraint(new OnAnd(new RequiresCompleteForNonHorn<bool>()));
    _bfnt.addProblemConstraint(notWithCat(Property::EPR));
    _bfnt.setRandomChoices({},{"on","off","off","off","off","off"});
    _bfnt.setExperimental();
    
    _increasedNumeralWeight = BoolOptionValue("increased_numeral_weight","inw",false);
    _increasedNumeralWeight.description=
             "This option only applies if the problem has interpreted numbers. The weight of integer constants depends on the logarithm of their absolute value (instead of being 1)";
    _lookup.insert(&_increasedNumeralWeight);
    _increasedNumeralWeight.tag(OptionTag::SATURATION);


    _interpretedSimplification = BoolOptionValue("interpreted_simplification","",false);
    _interpretedSimplification.description=
             "Performs simplifications of interpreted functions. This option requires interpreted_evaluation to be enabled as well. IMPORTANT - Currently not supported";
    _lookup.insert(&_interpretedSimplification);
    _interpretedSimplification.tag(OptionTag::OTHER);
    _interpretedSimplification.setExperimental();


    _literalComparisonMode = ChoiceOptionValue<LiteralComparisonMode>("literal_comparison_mode","lcm",
                                                                      LiteralComparisonMode::STANDARD,
                                                                      {"predicate","reverse","standard"});
    _literalComparisonMode.description="Vampire uses term orderings which use an ordering of predicates. Standard places equality (and certain other special predicates) first and all others second. Predicate depends on symbol precedence (see symbol_precedence). Reverse reverses the order.";
    _lookup.insert(&_literalComparisonMode);
    _literalComparisonMode.tag(OptionTag::SATURATION);
    _literalComparisonMode.addProblemConstraint(hasNonUnits());
    _literalComparisonMode.addProblemConstraint(hasPredicates());
    // TODO: if sat then should not use reverse
    _literalComparisonMode.setRandomChoices({"predicate","reverse","standard"});


    _maxActive = LongOptionValue("max_active","",0);
    _maxActive.description="";
    //_lookup.insert(&_maxActive);
    _maxActive.tag(OptionTag::OTHER);

    _maxAnswers = IntOptionValue("max_answers","",1);
    _maxAnswers.description="";
    //_lookup.insert(&_maxAnswers);
    _maxAnswers.tag(OptionTag::OTHER);

    _maxInferenceDepth = IntOptionValue("max_inference_depth","",0);
    _maxInferenceDepth.description="";
    //_lookup.insert(&_maxInferenceDepth);
    _maxInferenceDepth.tag(OptionTag::OTHER);

    _maxPassive = LongOptionValue("max_passive","",0);
    _maxPassive.description="";
    //_lookup.insert(&_maxPassive);
    _maxPassive.tag(OptionTag::OTHER);

    _nonGoalWeightCoefficient = NonGoalWeightOptionValue("nongoal_weight_coefficient","nwc",1.0);
    _nonGoalWeightCoefficient.description=
             "coefficient that will multiply the weight of theory clauses (those marked as 'axiom' in TPTP)";
    _lookup.insert(&_nonGoalWeightCoefficient);
    _nonGoalWeightCoefficient.tag(OptionTag::SATURATION);
    _nonGoalWeightCoefficient.setRandomChoices({"1","1.1","1.2","1.3","1.5","1.7","2","2.5","3","4","5","10"});

    _restrictNWCtoGC = BoolOptionValue("restrict_nwc_to_goal_constants","rnwc",false);
    _restrictNWCtoGC.description = "restrict nongoal_weight_coefficient to those containing goal constants";
    _lookup.insert(&_restrictNWCtoGC);
    _restrictNWCtoGC.tag(OptionTag::SATURATION);
    _restrictNWCtoGC.setExperimental();
    _restrictNWCtoGC.reliesOn(_nonGoalWeightCoefficient.is(notEqual(1.0f)));


    _normalize = BoolOptionValue("normalize","norm",false);
    _normalize.description="Normalize the problem so that the ordering of clauses etc does not effect proof search.";
    _lookup.insert(&_normalize);
    _normalize.tag(OptionTag::PREPROCESSING);

    _questionAnswering = ChoiceOptionValue<QuestionAnsweringMode>("question_answering","qa",QuestionAnsweringMode::OFF,
                                                                  {"answer_literal","from_proof","off"});
    _questionAnswering.description="Determines whether (and how) we attempt to answer questions";
    _questionAnswering.addHardConstraint(If(notEqual(QuestionAnsweringMode::OFF)).then(_splitting.is(notEqual(true))));
    _lookup.insert(&_questionAnswering);
    _questionAnswering.tag(OptionTag::OTHER);

    _randomSeed = IntOptionValue("random_seed","",Random::seed());
    _randomSeed.description="Some parts of vampire use random numbers. This seed allows for reproducability of results. By default the seed is not changed.";
    _lookup.insert(&_randomSeed);
    _randomSeed.tag(OptionTag::INPUT);

    _activationLimit = IntOptionValue("activation_limit","al",0);
    _activationLimit.description="Terminate saturation after this many iterations of the main loop. 0 means no limit.";
    _activationLimit.setExperimental();
    _lookup.insert(&_activationLimit);

    _termOrdering = ChoiceOptionValue<TermOrdering>("term_ordering","to", TermOrdering::KBO,
                                                    {"kbo","lpo"});
    _termOrdering.description="The term ordering used by Vampire to orient equations and order literals";
    _termOrdering.tag(OptionTag::SATURATION);
    _lookup.insert(&_termOrdering);

    _symbolPrecedence = ChoiceOptionValue<SymbolPrecedence>("symbol_precedence","sp",SymbolPrecedence::ARITY,
                                                            {"arity","occurrence","reverse_arity","scramble",
                                                             "frequency","reverse_frequency",
                                                             "weighted_frequency","reverse_weighted_frequency"});
    _symbolPrecedence.description="Vampire uses term orderings which require a precedence relation between symbols. Arity orders symbols by their arity (and reverse_arity takes the reverse of this) and occurence orders symbols by the order they appear in the problem.";
    _lookup.insert(&_symbolPrecedence);
    _symbolPrecedence.tag(OptionTag::SATURATION);
    _symbolPrecedence.setRandomChoices({"arity","occurence","reverse_arity","frequency"});

    _introducedSymbolPrecedence = ChoiceOptionValue<IntroducedSymbolPrecedence>("introduced_symbol_precedence","isp",
                                                                                IntroducedSymbolPrecedence::TOP,
                                                                                {"top","bottom"});
    _introducedSymbolPrecedence.description="Decides where to place symbols introduced during proof search in the symbol precedence";
    _lookup.insert(&_introducedSymbolPrecedence);
    _introducedSymbolPrecedence.tag(OptionTag::SATURATION);

    _functionPrecedence = StringOptionValue("function_precendence","fp","");
    _functionPrecedence.description = "A name of a file with an explicit user specified precedence on function symbols.";
    _functionPrecedence.setExperimental();
    _lookup.insert(&_functionPrecedence);

    _predicatePrecedence = StringOptionValue("predicate_precendence","pp","");
    _predicatePrecedence.description = "A name of a file with an explicit user specified precedence on predicate symbols.";
    _predicatePrecedence.setExperimental();
    _lookup.insert(&_predicatePrecedence);

    _symbolPrecedenceBoost = ChoiceOptionValue<SymbolPrecedenceBoost>("symbol_precedence_boost","spb",SymbolPrecedenceBoost::NONE,
                                     {"none","goal","units","goal_then_units"});
    _symbolPrecedenceBoost.description = "";
    _symbolPrecedenceBoost.tag(OptionTag::SATURATION);
    _lookup.insert(&_symbolPrecedenceBoost);

    _weightIncrement = BoolOptionValue("weight_increment","",false);
    _weightIncrement.description="";
    //_lookup.insert(&_weightIncrement);
    _weightIncrement.tag(OptionTag::OTHER);


    //******************************************************************
    //*********************** Vinter???  *******************************
    //******************************************************************

    
    _colorUnblocking = BoolOptionValue("color_unblocking","",false);
    _colorUnblocking.description="";
    _lookup.insert(&_colorUnblocking);
    _colorUnblocking.setExperimental();
    _colorUnblocking.tag(OptionTag::OTHER);
    
    
    _showInterpolant = ChoiceOptionValue<InterpolantMode>("show_interpolant","",InterpolantMode::OFF,
                                                          {"new_heur","new_opt","off", "old", "old_opt"});
    _lookup.insert(&_showInterpolant);
    _showInterpolant.tag(OptionTag::OTHER);
    _showInterpolant.setExperimental();

//******************************************************************
//*********************** Bound Propagation  ***********************
//******************************************************************
    
/*
    _whileNumber = IntOptionValue("while_number","",1);
    _whileNumber.description="";
    _lookup.insert(&_whileNumber);
    _whileNumber.tag(Mode::BOUND_PROP);
    
    _functionNumber = IntOptionValue("function_number","",1);
    _functionNumber.description="";
    _lookup.insert(&_functionNumber);
    _functionNumber.tag(Mode::BOUND_PROP);
    _functionNumber.tag(OptionTag::PREPROCESSING);
    
    _bpCollapsingPropagation = BoolOptionValue("bp_add_collapsing_inequalities","",false); // ASSUMED default, wasn't in Options
    _bpCollapsingPropagation.description="";
    _lookup.insert(&_bpCollapsingPropagation);
    _bpCollapsingPropagation.tag(Mode::BOUND_PROP);
    _bpCollapsingPropagation.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpAllowedFMBalance = UnsignedOptionValue("bp_allowed_fm_balance","",0);
    _bpAllowedFMBalance.description="";
    _lookup.insert(&_bpAllowedFMBalance);
    _bpAllowedFMBalance.tag(Mode::BOUND_PROP);
    _bpAllowedFMBalance.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpAlmostHalfBoundingRemoval= ChoiceOptionValue<BPAlmostHalfBoundingRemoval>("bp_almost_half_bounding_removal","",
                                                                                 BPAlmostHalfBoundingRemoval::ON,{"bounds_on","off","on"});
    _bpAlmostHalfBoundingRemoval.description="";
    _lookup.insert(&_bpAlmostHalfBoundingRemoval);
    _bpAlmostHalfBoundingRemoval.tag(Mode::BOUND_PROP);
    _bpAlmostHalfBoundingRemoval.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpAssignmentSelector = ChoiceOptionValue<BPAssignmentSelector>("bp_assignment_selector","",
                                                                    BPAssignmentSelector::RANDOM,
                                                                    {"alternating","bmp","lower_bound",
                                                                        "middle","random","rational","smallest",
                                                                        "tight","tightish","upper_bound"});
    _bpAssignmentSelector.description="";
    _lookup.insert(&_bpAssignmentSelector);
    _bpAssignmentSelector.tag(Mode::BOUND_PROP);
    _bpAssignmentSelector.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _updatesByOneConstraint= UnsignedOptionValue("bp_bound_improvement_limit","",3);
    _updatesByOneConstraint.description="";
    _lookup.insert(&_updatesByOneConstraint);
    _updatesByOneConstraint.tag(Mode::BOUND_PROP);
    _updatesByOneConstraint.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpConflictSelector = ChoiceOptionValue<BPConflictSelector>("bp_conflict_selector","",
                                                                BPConflictSelector::MOST_RECENT,{"least_recent","most_recent","shortest"});
    _bpConflictSelector.description="";
    _lookup.insert(&_bpConflictSelector);
    _bpConflictSelector.tag(Mode::BOUND_PROP);
    _bpConflictSelector.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpConservativeAssignmentSelection = BoolOptionValue("bp_conservative_assignment_selection","",true);
    _bpConservativeAssignmentSelection.description="";
    _lookup.insert(&_bpConservativeAssignmentSelection);
    _bpConservativeAssignmentSelection.tag(Mode::BOUND_PROP);
    _bpConservativeAssignmentSelection.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpFmElimination= BoolOptionValue("bp_fm_elimination","",true);
    _bpFmElimination.description="";
    _lookup.insert(&_bpFmElimination);
    _bpFmElimination.tag(Mode::BOUND_PROP);
    _bpFmElimination.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _maximalPropagatedEqualityLength = UnsignedOptionValue("bp_max_prop_length","",5);
    _maximalPropagatedEqualityLength.description="";
    _lookup.insert(&_maximalPropagatedEqualityLength);
    _maximalPropagatedEqualityLength.tag(Mode::BOUND_PROP);
    _maximalPropagatedEqualityLength.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpPropagateAfterConflict = BoolOptionValue("bp_propagate_after_conflict","",true);
    _bpPropagateAfterConflict.description="";
    _lookup.insert(&_bpPropagateAfterConflict);
    _bpPropagateAfterConflict.tag(Mode::BOUND_PROP);
    _bpPropagateAfterConflict.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpStartWithPrecise = BoolOptionValue("bp_start_with_precise","",false);
    _bpStartWithPrecise.description="";
    _lookup.insert(&_bpStartWithPrecise);
    _bpStartWithPrecise.tag(Mode::BOUND_PROP);
    _bpStartWithPrecise.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpStartWithRational = BoolOptionValue("bp_start_with_rational","",false);
    _bpStartWithRational.description="";
    _lookup.insert(&_bpStartWithRational);
    _bpStartWithRational.tag(Mode::BOUND_PROP);
    _bpStartWithRational.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
    
    _bpVariableSelector = ChoiceOptionValue<BPVariableSelector>("bp_variable_selector","",
                                                                BPVariableSelector::TIGHTEST_BOUND,
                                                                {"conflicting","conflicting_and_collapsing",
                                                                    "first","look_ahead","random","recent_collapsing",
                                                                    "recent_conflicting","tightest_bound"});
    _bpVariableSelector.description="";
    _lookup.insert(&_bpVariableSelector);
    _bpVariableSelector.tag(Mode::BOUND_PROP);
    _bpVariableSelector.reliesOn(_mode.is(equal(Mode::BOUND_PROP)));
*/

    
 // Declare tag names
    
    _tagNames = {
                 "Unused",
                 "Other",
                 "Development",
                 "Output",
                 "Instance Generation",
                 "SAT Solving",
                 "AVATAR",
                 "Inferences",
                 "LRS Specific",
                 "Saturation",
                 "Preprocessing",
                 "Input",
                 "Help",
                 "Global"
                };

} // Options::init

void Options::copyValuesFrom(const Options& that)
{
  //copy across the actual values in that
  VirtualIterator<AbstractOptionValue*> options = _lookup.values();

  while(options.hasNext()){
    AbstractOptionValue* opt = options.next();
    if(opt->shouldCopy()){
      AbstractOptionValue* other = that.getOptionValueByName(opt->longName);
      ASS(opt!=other);
      bool status = opt -> set(other->getStringOfActual());
      ASS(status);
    }
  }
}
Options::Options(const Options& that)
{
  init();
  copyValuesFrom(that);
}

Options& Options::operator=(const Options& that)
{
  if(this==&that) return *this;
  copyValuesFrom(that);
  return *this;
}


/**
 * Set option by its name and value.
 * @since 13/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing
 * @since 14/09/2014 updated to use _lookup
 * @author Andrei Voronkov
 */
void Options::set(const char* name,const char* value, bool longOpt)
{
  CALL ("Options::set/3");

  try {
    if((longOpt && !_lookup.findLong(name)->set(value)) ||
        (!longOpt && !_lookup.findShort(name)->set(value))) {
      switch (ignoreMissing()) {
      case IgnoreMissing::OFF:
        USER_ERROR((vstring) value +" is an invalid value for "+(vstring)name+"\nSee help or use explain i.e. vampire -explain mode");
        break;
      case IgnoreMissing::WARN:
        if (outputAllowed()) {
          env.beginOutput();
          addCommentSignForSZS(env.out());
          env.out() << "WARNING: invalid value "<< value << " for option " << name << endl;
          env.endOutput();
        }
        break;
      case IgnoreMissing::ON:
        break;
      }
    }
  }
  catch (const ValueNotFoundException&) {
    if (_ignoreMissing.actualValue != IgnoreMissing::ON) {
      vstring msg = (vstring)name + (longOpt ? " is not a valid option" : " is not a valid short option (did you mean --?)");
      if (_ignoreMissing.actualValue == IgnoreMissing::WARN) {
        if (outputAllowed()) {
          env.beginOutput();
          addCommentSignForSZS(env.out());
          env.out() << "WARNING: " << msg << endl;
          env.endOutput();
        }
        return;
      } // else:
      Stack<vstring> sim = getSimilarOptionNames(name,false);
      Stack<vstring>::Iterator sit(sim);
      if(sit.hasNext()){
        vstring first = sit.next();
        msg += "\n\tMaybe you meant ";
        if(sit.hasNext()) msg += "one of:\n\t\t";
        msg += first;
        while(sit.hasNext()){ msg+="\n\t\t"+sit.next();}
        msg+="\n\tYou can use -explain <option> to explain an option";
      }
      USER_ERROR(msg);
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
  set(name.c_str(),value.c_str(),true);
} // Options::set/2

bool Options::OptionHasValue::check(Property*p){
          CALL("Options::OptionHasValue::check");
          AbstractOptionValue* opt = env.options->getOptionValueByName(option_value);
          ASS(opt);
          return opt->getStringOfActual()==value;
}

/**
 * Static functions to help specify random choice values
 */

Options::OptionProblemConstraint* Options::isRandOn(){
      return new OptionHasValue("random_strategy","on");
}
Options::OptionProblemConstraint* Options::isRandSat(){
      return new OptionHasValue("random_strategy","sat");
}
Options::OptionProblemConstraint* Options::saNotInstGen(){
      return new OptionHasValue("sa","inst_gen");
}
Options::OptionProblemConstraint* Options::isBfnt(){
      return new OptionHasValue("bfnt","on");
}

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

  if(printAllTheoryAxioms()){
    cout << "Sorry, not implemented yet!" << endl;

    return;
  }

  if(!explainOption().empty()){

    //We bypass the allocator here because of the use of vstringstream
    BYPASSING_ALLOCATOR;

     AbstractOptionValue* option;
     vstring name = explainOption();
     try{
       option = _lookup.findLong(name);
     }
     catch(const ValueNotFoundException&){ 
       try{
         option = _lookup.findShort(name);
       }
       catch(const ValueNotFoundException&){
         option = 0;
       }
     }
     if(!option){ 
       str << name << " not a known option" << endl;
       Stack<vstring> sim_s = getSimilarOptionNames(name,true);
       Stack<vstring> sim_l = getSimilarOptionNames(name,false);
       VirtualIterator<vstring> sit = pvi(getConcatenatedIterator(
           Stack<vstring>::Iterator(sim_s),Stack<vstring>::Iterator(sim_l))); 
        if(sit.hasNext()){
          vstring first = sit.next();
          str << "\tMaybe you meant ";
          if(sit.hasNext()) str << "one of:\n\t\t";
          str << first;
          while(sit.hasNext()){ str << "\n\t\t"+sit.next();}
          str << endl;
        }
     }
     else{
       vstringstream vs;
       option->output(vs);
       str << vs.str();
     }

  }

  if (showHelp()){
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

  bool normalshow = showOptions();
  bool experimental = showExperimentalOptions();  
  
  if(normalshow || experimental) {

    //We bypass the allocator here because of the use of vstringstream
    BYPASSING_ALLOCATOR;

    Mode this_mode = _mode.actualValue;
    //str << "=========== Options ==========\n";

    VirtualIterator<AbstractOptionValue*> options = _lookup.values();

    //Stack<vstringstream*> groups;
    int num_tags = static_cast<int>(OptionTag::LAST_TAG);
    Stack<Stack<AbstractOptionValue*>> groups;
    for(int i=0; i<=num_tags;i++){
    //  groups.push(new vstringstream);
        Stack<AbstractOptionValue*> stack;
        groups.push(stack);
    }


    while(options.hasNext()){
      AbstractOptionValue* option = options.next();
      if(option->inMode(this_mode) && 
              ((experimental && option->experimental) || 
               (normalshow && !option->experimental) )){
        unsigned tag = static_cast<unsigned>(option->getTag());
        //option->output(*groups[tag]);
        (groups[tag]).push(option);
      }
    }

    //output them in reverse order
    for(int i=num_tags;i>=0;i--){
      if(groups[i].isEmpty()) continue;
      vstring label = "  "+_tagNames[i]+"  ";
      ASS(label.length() < 40);
      vstring br = "******************************";
      vstring br_gap = br.substr(0,(br.length()-(label.length()/2)));
      str << endl << br << br << endl;
      str << br_gap << label << br_gap << endl;
      str << br << br << endl << endl;

      // Sort
      Stack<AbstractOptionValue*> os = groups[i];
      DArray<AbstractOptionValue*> osa;
      osa.initFromIterator(Stack<AbstractOptionValue*>::Iterator(os));
      osa.sort(AbstractOptionValueCompatator());
      DArray<AbstractOptionValue*>::Iterator oit(osa);
      while(oit.hasNext()){
        oit.next()->output(str);
      }
      //str << (*groups[i]).str();
      //BYPASSING_ALLOCATOR;
      //delete groups[i];
    }

    //str << "======= End of options =======\n";
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

template<typename T>
bool Options::OptionValue<T>::randomize(Property* prop){
  CALL("Options::OptionValue::randomize()");

  DArray<vstring>* choices = 0;
  if(env.options->randomStrategy()==RandomStrategy::NOCHECK) prop=0;

  // Only randomize if we have a property and need it or don't have one and don't need it!
  if( env.options->randomStrategy()!=RandomStrategy::NOCHECK && 
      ((prop && !hasProblemConstraints()) || (!prop && hasProblemConstraints()))
    ){
    return false;
  }
  // Note that if we supressed the problem constraints
  // the checks will be skipped

  //Search for the first set of random choices that is valid
  Stack<RandEntry>::BottomFirstIterator entry_it(rand_choices);
  while(entry_it.hasNext()){
    auto entry = entry_it.next();
    if(!entry.first || (prop && entry.first->check(prop))){
      choices = entry.second;
    }  
  }
  if(!choices || choices->size()==0) return false; // no valid choices

  //Pick a random option from the available choices
  int index = Random::getInteger(choices->size());
  set((*choices)[index]);
  return true;
}

//TODO should not use cout, should use env.out
template<typename T>
bool Options::OptionValue<T>::checkConstraints(){
     CALL("Options::OptionValue::checkConstraints");
     typename Lib::Stack<OptionValueConstraint<T>*>::Iterator it(_constraints);
     while(it.hasNext()){
       OptionValueConstraint<T>* con = it.next();
       if(!con->check(this)){

         if(env.options->mode()==Mode::SPIDER){
           reportSpiderFail();
           USER_ERROR("\nBroken Constraint: "+con->msg(this));
         }

         if(con->isHard()){ 
           if(env.options->randomStrategy()!=RandomStrategy::OFF)
              return false; // Skip warning for Hard
           USER_ERROR("\nBroken Constraint: "+con->msg(this)); 
         }
         switch(env.options->getBadOptionChoice()){
           case BadOption::HARD :
               USER_ERROR("\nBroken Constraint: "+con->msg(this));
           case BadOption::SOFT :
               cout << "WARNING Broken Constraint: "+con->msg(this) << endl;
               return false;
           case BadOption::FORCED :
               if(con->force(this)){
                 cout << "Forced constraint " + con->msg(this) << endl;
                 break;
               }else{
                 USER_ERROR("\nCould not force Constraint: "+con->msg(this));
               }
           case BadOption::OFF: 
             return false;
           default: ASSERTION_VIOLATION;
        }
     }
    }
    return true;
}

template<typename T>
bool Options::OptionValue<T>::checkProblemConstraints(Property* prop){
    CALL("Options::OptionValue::checkProblemConstraints");

    Lib::Stack<OptionProblemConstraint*>::Iterator it(_prob_constraints);
    while(it.hasNext()){
      OptionProblemConstraint* con = it.next();
      // Constraint should hold whenever the option is set
      if(is_set && !con->check(prop)){

         if(env.options->mode()==Mode::SPIDER){
           reportSpiderFail();
           USER_ERROR("WARNING: " + longName + con->msg());
         }

         switch(env.options->getBadOptionChoice()){
         case BadOption::OFF: break;
         default:
           cout << "WARNING: " << longName << con->msg() << endl;
         }
         return false;
      }
    }
    return true;
}


template<typename T>
Options::WrappedConstraint<T>* Options::OptionValue<T>::is(OptionValueConstraint<T>* c)
{
    return new WrappedConstraint<T>(this,c);
}

template<typename T>
template<typename S, typename R>
Options::OptionValueConstraint<S>* Options::WrappedConstraint<T>::And(WrappedConstraint<R>* another)
{
    return new AndWrapper<S>(new UnWrappedConstraint<S,T>(this), new UnWrappedConstraint<S,R>(another));
}
template<typename T>
template<typename S, typename R>
Options::OptionValueConstraint<S>* Options::WrappedConstraint<T>::Or(WrappedConstraint<R>* another)
{
    return new OrWrapper<S>(new UnWrappedConstraint<S,T>(this), new UnWrappedConstraint<S,R>(another));
}

template<typename T>
Options::OptionValueConstraint<T>* Options::OptionValueConstraint<T>::And(OptionValueConstraint<T>* another)
{
    return new AndWrapper<T>(this,another);
}
template<typename T>
Options::OptionValueConstraint<T>* Options::OptionValueConstraint<T>::Or(OptionValueConstraint<T>* another)
{
    return new OrWrapper<T>(this,another);
}
template<typename T>
template<typename S>
Options::OptionValueConstraint<T>* Options::OptionValueConstraint<T>::And(WrappedConstraint<S>* another)
{
    return new AndWrapper<T>(this,new UnWrappedConstraint<T,S>(another));
}
template<typename T>
template<typename S>
Options::OptionValueConstraint<T>* Options::OptionValueConstraint<T>::Or(WrappedConstraint<S>* another)
{
    return new OrWrapper<T>(this,new UnWrappedConstraint<T,S>(another));
}

/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are integers.
 *
 * @since 25/05/2004 Manchester
 */
bool Options::RatioOptionValue::readRatio(const char* val, char separator)
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
      return false;
    }
    char copy[128];
    strcpy(copy,val);
    copy[colonIndex] = 0;
    int age;
    if (! Int::stringToInt(copy,age)) {
      return false;
    }
    actualValue = age;
    int weight;
    if (! Int::stringToInt(copy+colonIndex+1,weight)) {
      return false;
    }
    otherValue = weight;

    // don't allow ratios 0:0
    if (actualValue == 0 && otherValue == 0) {
      return false;
    }

    return true;
  }
  actualValue = 1;
  int weight;
  if (! Int::stringToInt(val,weight)) {
    return false;
  }
  otherValue = weight;
  return true;
}

bool Options::NonGoalWeightOptionValue::setValue(const vstring& value)
{
  CALL("NonGoalWeightOptionValue::setValue");

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

bool Options::SelectionOptionValue::setValue(const vstring& value)
{
  CALL("SelectionOptionValue::setValue");

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
  case 20:
  case 21:
  case 22:

  case 30:
  case 31:
  case 32:
  case 33:
  case 34:
  case 35:

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
  case -20: // almost same as 20 (but factoring will be on negative and not positive literals)
  case -21:
  case -22:
  case -30: // almost same as 30 (but factoring will be on negative and not positive literals)
  case -31:
  case -32:
  case -33:
  case -34:
  case -35:

  case -1002:
  case -1003:
  case -1004:
  case -1010:
  case -1011: // almost same as 1011 (but factoring will be on negative and not positive literals)
    actualValue = sel;
    return true;
  default:
    return false;
  }
}

bool Options::InputFileOptionValue::setValue(const vstring& value)
{
  CALL("InputFileOptionValue::setValue");

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


bool Options::TimeLimitOptionValue::setValue(const vstring& value)
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
  float multiplier = 10.0; // by default assume seconds
  switch (*end) {
  case 'd': // deciseconds
      multiplier = 1.0;
      *end = 0;
      break;
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
  case 'D': // days
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

  return true;
} // Options::readTimeLimit(const char* val)

void Options::randomizeStrategy(Property* prop)
{
  CALL("Options::randomizeStrategy");
  if(_randomStrategy.actualValue==RandomStrategy::OFF) return;

  TimeCounter tc(TC_RAND_OPT);

  // The pseudo random sequence is deterministic given a seed.
  // By default the seed is 1
  // For this randomisation we get save the seed and try and randomize it
  int saved_seed = Random::seed();
  Random::setSeed(time(NULL)); // TODO is this the best choice of seed?

  // We randomize options that have setRandomChoices
  // TODO: randomize order in which options are selected
  //       (not order of insertion but probably deterministic)

  // We define some options that should be set before the rest
  // Note this is a stack!
  Stack<AbstractOptionValue*> do_first;
  do_first.push(&_saturationAlgorithm);
  do_first.push(&_bfnt);

  auto options = getConcatenatedIterator(Stack<AbstractOptionValue*>::Iterator(do_first),_lookup.values());

  // whilst doing this don't report any bad options
  BadOption saved_bad_option = _badOption.actualValue;
  _badOption.actualValue=BadOption::OFF;

  bool skipChecks = _randomStrategy.actualValue == RandomStrategy::NOCHECK;

  while(options.hasNext()){
    AbstractOptionValue* option = options.next();
    if(!option->is_set){
      // try 5 random values before giving up
      vstring def = option->getStringOfActual();

      // This is where we check the NoProperty condition if prop=0
      bool can_rand = option->randomize(prop);
      // If we cannot randomize then skip (invariant, if this is false value is unchanged)
      if(can_rand){
        // We need to check ALL constraints - rather inefficient
        bool valid = skipChecks || (checkGlobalOptionConstraints(true) && (!prop || checkProblemOptionConstraints(prop,true)));
        unsigned i=4;
        while(!valid && i-- > 0){
          option->randomize(prop);
          valid = checkGlobalOptionConstraints(true) && (!prop || checkProblemOptionConstraints(prop,true));
        }
        if(!valid){
           //cout << "Failed for " << option->longName << endl;
           option->set(def);
           option->is_set=false;
        }
        //else cout << "Randomized " << option->longName << endl;
      }// else cout << "cannot randomize " << option->longName << endl;
    }
  }

  // Reset saved things
  _badOption.actualValue = saved_bad_option;
  Random::setSeed(saved_seed);

  //When we reach this place all constraints should be holding
  //However, there is one we haven't checked yet: bfnt completeness
  //If this fails we restart this with bfnt set to off... only if it was on before
  if(!checkGlobalOptionConstraints() && _bfnt.actualValue){
    _bfnt.set("off");
    randomizeStrategy(prop);
  }
  else{
    if(prop) cout << "Random strategy: " + generateEncodedOptions() << endl;
  }
}

/**
 * Assign option values as encoded in the option vstring if assign=true, otherwise check that
 * the option values are not currently set to those values.
 * according to the argument in the format
 * opt1=val1:opt2=val2:...:optn=valN,
 * for example bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none
 */
void Options::readOptionsString(vstring optionsString,bool assign)
{
  CALL("Options::readOptionsString");

  // repeatedly look for param=value
  while (optionsString != "") {
    size_t index1 = optionsString.find('=');
    if (index1 == vstring::npos) {
      error: USER_ERROR("bad option specification '" + optionsString+"'");
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
    AbstractOptionValue* opt = getOptionValueByName(param);
    if(opt){
        if(assign){
            if (!opt->set(value)) {
              switch (ignoreMissing()) {
              case IgnoreMissing::OFF:
                USER_ERROR("value "+value+" for option "+ param +" not known");
                break;
              case IgnoreMissing::WARN:
                env.beginOutput();
                if (outputAllowed()) {
                  env.beginOutput();
                  addCommentSignForSZS(env.out());
                  env.out() << "WARNING: value " << value << " for option "<< param <<" not known" << endl;
                  env.endOutput();
                }
                break;
              case IgnoreMissing::ON:
                break;
              }
            }
        }
        else{
            vstring current = opt->getStringOfActual();
            if(value==current){
                USER_ERROR("option "+param+" uses forbidden value "+value);
            }
        }
    }
    else{
      switch (ignoreMissing()) {
      case IgnoreMissing::OFF:
        USER_ERROR("option "+param+" not known");
        break;
      case IgnoreMissing::WARN:
        env.beginOutput();
        if (outputAllowed()) {
          env.beginOutput();
          addCommentSignForSZS(env.out());
          env.out() << "WARNING: option "<< param << " not known." << endl;
          env.endOutput();
        }
        break;
      case IgnoreMissing::ON:
        break;
      }
    }

    if (index==vstring::npos) {
      return;
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
void Options::readFromEncodedOptions (vstring testId)
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
  else if (ma == "ins") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::INST_GEN;
  }
  else if (ma == "fmb") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::FINITE_MODEL_BUILDING;
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
  // setting assumes seconds as default, but encoded strings use deciseconds 
  _timeLimitInDeciseconds.actualValue = _timeLimitInDeciseconds.actualValue/10;

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
  _ageWeightRatio.set(awr.c_str());
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

  if(_forcedOptions.actualValue.empty()) return;
  readOptionsString(_forcedOptions.actualValue);
}

/**
 * Return testId vstring that represents current values of the options
 */
vstring Options::generateEncodedOptions() const
{
  CALL("Options::generateEncodedOptions");

  BYPASSING_ALLOCATOR;
  vostringstream res;
  //saturation algorithm
  vstring sat;
  switch(_saturationAlgorithm.actualValue){
    case SaturationAlgorithm::LRS : sat="lrs"; break;
    case SaturationAlgorithm::DISCOUNT : sat="dis"; break;
    case SaturationAlgorithm::OTTER : sat="ott"; break;
    case SaturationAlgorithm::INST_GEN : sat="ins"; break;
    case SaturationAlgorithm::FINITE_MODEL_BUILDING : sat="fmb"; break;
    default : ASSERTION_VIOLATION;
  }

  res << sat; 

  //selection function
  res << (selection() < 0 ? "-" : "+") << abs(selection());
  res << "_";

  //age-weight ratio
  if (ageRatio()!=1) {
    res << ageRatio() << ":";
  }
  res << weightRatio();
  res << "_";

  Options cur=*this;

  // Record options that do not want to be in encoded string
  static Set<const AbstractOptionValue*> forbidden;
  //we initialize the set if there's nothing inside
  if (forbidden.size()==0) {
    //things we output elsewhere
    forbidden.insert(&_saturationAlgorithm);
    forbidden.insert(&_selection);
    forbidden.insert(&_ageWeightRatio);
    forbidden.insert(&_timeLimitInDeciseconds);

    //things we don't want to output (showHelp etc won't get to here anyway)
    forbidden.insert(&_mode);
    forbidden.insert(&_testId); // is this old version of decode?
    forbidden.insert(&_include);
    forbidden.insert(&_problemName);
    forbidden.insert(&_inputFile);
    forbidden.insert(&_randomStrategy);
    forbidden.insert(&_decode);
    forbidden.insert(&_ignoreMissing); // or maybe we do!
  }

  VirtualIterator<AbstractOptionValue*> options = _lookup.values();

  bool first=true;
  while(options.hasNext()){
    AbstractOptionValue* option = options.next();
    // TODO do we want to also filter by !isDefault?
    if(!forbidden.contains(option) && option->is_set && !option->isDefault()){
      vstring name = option->shortName;
      if(name.empty()) name = option->longName;
      if(!first){ res<<":";}else{first=false;}
      res << name << "=" << option->getStringOfActual();
    }
  }

  if(!first){ res << "_"; }
  res << Lib::Int::toString(_timeLimitInDeciseconds.actualValue);
 
  return res.str();
 
}


/**
 * True if the options are complete.
 * @since 23/07/2011 Manchester
 */
bool Options::complete(const Problem& prb) const
{
  CALL("Options::complete");

  if (_showInterpolant.actualValue != InterpolantMode::OFF) {
    return false;
  }

  //we did some transformation that made us lose completeness
  //(e.g. equality proxy replacing equality for reflexive predicate)
  if (prb.hadIncompleteTransformation()) {
    return false;
  }

  Property& prop = *prb.getProperty();

  // general properties causing incompleteness
  if (prop.hasInterpretedOperations()
      || prop.hasProp(Property::PR_HAS_INTEGERS)
      || prop.hasProp(Property::PR_HAS_REALS)
      || prop.hasProp(Property::PR_HAS_RATS)
      || prop.hasProp(Property::PR_HAS_ARRAYS)
      || (!prop.onlyFiniteDomainDatatypes() && prop.hasProp(Property::PR_HAS_DT_CONSTRUCTORS))
      || (!prop.onlyFiniteDomainDatatypes() && prop.hasProp(Property::PR_HAS_CDT_CONSTRUCTORS))) {
    return false;
  }

  // preprocessing
  if (env.signature->hasDistinctGroups()) {
    return false;
  }

  switch (_saturationAlgorithm.actualValue) {
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
    if (_unitResultingResolution.actualValue!=URResolution::ON) return false;
    // binary resolution is off
    return prop.category() == Property::HNE; // URR is complete for Horn problems
  }

  if (!_demodulationRedundancyCheck.actualValue) return false;
  if (!_superpositionFromVariables.actualValue) return false;

  // only checking resolution rules remain
  bool pureEquality = (prop.atoms() == prop.equalityAtoms());
  if (pureEquality) return true;
  return (_binaryResolution.actualValue); // MS: we are in the equality case, so URR cannot help here even for horn problems
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


/**
 * Check constraints necessary for options to make sense
 *
 * The function is called after all options are parsed.
 */
bool Options::checkGlobalOptionConstraints(bool fail_early)
{
  CALL("Options::checkGlobalOptionsConstraints");

  //Check forbidden options
  readOptionsString(_forbiddenOptions.actualValue,false);
    
  //if we're not in mid-randomisation then check bfnt completeness
  //this assumes that fail_early is only on when being called from randomizeStrategy
  if(!fail_early && env.options->bfnt() && !completeForNNE()){
    return false;
  }

  bool result = true;

  // Check recorded option constraints
  VirtualIterator<AbstractOptionValue*> options = _lookup.values();
  while(options.hasNext()){ 
    result = options.next()->checkConstraints() && result; 
    if(fail_early && !result) return result;
  }

  return result;
}

/**
 * Check whether the option values make sense with respect to the given problem
 **/
bool Options::checkProblemOptionConstraints(Property* prop,bool fail_early)
{
   CALL("Options::checkProblemOptionConstraints");

  bool result = true;

  VirtualIterator<AbstractOptionValue*> options = _lookup.values();
  while(options.hasNext()){
    result = options.next()->checkProblemConstraints(prop) && result; 
    if(fail_early && !result) return result;
  }

  return result;
}

Lib::vvector<int> Options::theorySplitQueueRatios() const
{
  CALL("Options::theorySplitQueueRatios");
  vstringstream inputRatiosStream(_theorySplitQueueRatios.actualValue);
  Lib::vvector<int> inputRatios;
  std::string currentRatio;
  while (std::getline(inputRatiosStream, currentRatio, ',')) {
    inputRatios.push_back(std::stoi(currentRatio));
  }

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-thsqr'. Needs to have at least two values (e.g. '10,1')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Wrong usage of option '-thsqr'. Each ratio needs to be a positive integer");
    }
  }

  return inputRatios;
}

Lib::vvector<float> Options::theorySplitQueueCutoffs() const
{
  CALL("Options::theorySplitQueueCutoffs");
  // initialize cutoffs
  Lib::vvector<float> cutoffs;
  if (_theorySplitQueueCutoffs.isDefault()) {
    // if no custom cutoffs are set, use heuristics: (0,4*d,10*d,infinity)
    auto d = _theorySplitQueueExpectedRatioDenom.actualValue;
    cutoffs.push_back(0.0f);
    cutoffs.push_back(4.0f * d);
    cutoffs.push_back(10.0f * d);
    cutoffs.push_back(std::numeric_limits<float>::max());
  } else {
    // if custom cutoffs are set, parse them and add float-max as last value
    vstringstream cutoffsStream(_theorySplitQueueCutoffs.actualValue);
    std::string currentCutoff;
    while (std::getline(cutoffsStream, currentCutoff, ','))
    {
      cutoffs.push_back(std::stof(currentCutoff));
    }
    cutoffs.push_back(std::numeric_limits<float>::max());
  }

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("Wrong usage of option '-thsqc'. The cutoff values must be strictly increasing");
    }
  }

  return cutoffs;
}

Lib::vvector<int> Options::avatarSplitQueueRatios() const
{
  CALL("Options::avatarSplitQueueRatios");
  vstringstream inputRatiosStream(_avatarSplitQueueRatios.actualValue);
  Lib::vvector<int> inputRatios;
  std::string currentRatio;
  while (std::getline(inputRatiosStream, currentRatio, ',')) {
    inputRatios.push_back(std::stoi(currentRatio));
  }

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-avsqr'. Needs to have at least two values (e.g. '10,1')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Each ratio (supplied by option '-avsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

Lib::vvector<float> Options::avatarSplitQueueCutoffs() const
{
  CALL("Options::avatarSplitQueueCutoffs");
  // initialize cutoffs and add float-max as last value
  Lib::vvector<float> cutoffs;
  vstringstream cutoffsStream(_avatarSplitQueueCutoffs.actualValue);
  std::string currentCutoff;
  while (std::getline(cutoffsStream, currentCutoff, ','))
  {
    cutoffs.push_back(std::stof(currentCutoff));
  }
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-avsqc') must be strictly increasing");
    }
  }

  return cutoffs;
}

Lib::vvector<int> Options::sineLevelSplitQueueRatios() const
{
  CALL("Options::sineLevelSplitQueueRatios");
  vstringstream inputRatiosStream(_sineLevelSplitQueueRatios.actualValue);
  Lib::vvector<int> inputRatios;
  std::string currentRatio;
  while (std::getline(inputRatiosStream, currentRatio, ',')) {
    inputRatios.push_back(std::stoi(currentRatio));
  }

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-slsqr'. Needs to have at least two values (e.g. '1,3')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Each ratio (supplied by option '-slsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

Lib::vvector<float> Options::sineLevelSplitQueueCutoffs() const
{
  CALL("Options::sineLevelSplitQueueCutoffs");
  // initialize cutoffs and add float-max as last value
  Lib::vvector<float> cutoffs;
  vstringstream cutoffsStream(_sineLevelSplitQueueCutoffs.actualValue);
  std::string currentCutoff;
  while (std::getline(cutoffsStream, currentCutoff, ','))
  {
    cutoffs.push_back(std::stof(currentCutoff));
  }
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-slsqc') must be strictly increasing");
    }
  }

  return cutoffs;
}
