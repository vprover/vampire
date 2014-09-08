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
 * Class to hide various data used by class Options, mostly name arrays.
 * @since 21/04/2005 Manchester
 */
class Options::Constants {
public:

  static const OptionName _optionNames[];
  static OptionNameArray optionNames;
}; // class Options::Constants


/** Names for all options */
const OptionName Options::Constants::_optionNames[] = {
  OptionName("age_weight_ratio","awr",
             "Ratio in which clauses are being selected for activation i.e. a:w means that for every a clauses selected based on age there will be w selected based on weight.",
             false, "1:1"), 
  OptionName("aig_bdd_sweeping","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("aig_conditional_rewriting","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("aig_definition_introduction","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("aig_definition_introduction_threshold","",GLOBAL_TAG,
             "number of subformula occurrences needed to introduce a name for it (if aig_definition_introduction is enabled)",
             false, "4"),
  OptionName("aig_formula_sharing","",GLOBAL_TAG,
             "Detection and sharing of common subformulas using AIG representation",
             false, "false"),
  OptionName("aig_inliner","",GLOBAL_TAG,
             "",
             false,"false"),
  OptionName("arity_check","",GLOBAL_TAG,
             "The same symbol name cannot be used with multiple arities",
             false, "false"),

  OptionName("backward_demodulation","bd",GLOBAL_TAG,
             "Oriented rewriting of kept clauses by newly derived unit equalities\n"
             "s = t     L[sθ] \\/ C\n"
             "---------------------   where sθ > tθ (replaces RHS)\n"
             " L[tθ] \\/ C\n",
             false,"all", OptionValues("all","off","preordered")),
  OptionName("backward_subsumption","bs",GLOBAL_TAG,
             "unit_only means that the subsumption will be performed only by unit clauses",
             false, "on", OptionValues("off","on","unit_only")),
  OptionName("backward_subsumption_resolution","bsr",GLOBAL_TAG,
             "unit_only means that the subsumption resolution will be performed only by unit clauses",
             false, "off", OptionValues("off","on","unit_only")),
  OptionName("bfnt","bfnt",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("binary_resolution","br",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("bp_add_collapsing_inequalities","",BP_TAG,
             "",
             false), // no default?
  OptionName("bp_allowed_fm_balance","",BP_TAG,
             "",
             false, "0"),
  OptionName("bp_almost_half_bounding_removal","",BP_TAG,
             "",
             false, "on",OptionValues("bounds_on","off","on")),
  OptionName("bp_assignment_selector","",BP_TAG,
             "",
             false, "random", OptionValues("alternating","bmp","lower_bound",
                                     "middle","random","rational","smallest",
                                     "tight","tightish","upper_bound")),
  OptionName("bp_bound_improvement_limit","",BP_TAG,
             "",
             false), // no default?
  OptionName("bp_conflict_selector","",BP_TAG,
             "",
             false, "most_recent", OptionValues("least_recent","most_recent","shortest")),
  OptionName("bp_conservative_assignment_selection","",BP_TAG,
             "",
             false, "true"),
  OptionName("bp_fm_elimination","",BP_TAG,
             "",
             false, "true"),
  OptionName("bp_max_prop_length","",BP_TAG,
             "",
             false), // no default?
  OptionName("bp_propagate_after_conflict","",BP_TAG,
             "",
             false, "true"),
  OptionName("bp_start_with_precise","",BP_TAG,
             "",
             false, "false"),
  OptionName("bp_start_with_rational","",BP_TAG,
             "",
             false, "false"),
  OptionName("bp_variable_selector","",BP_TAG,
             "",
             false, "tightest_bound",
                       OptionValues("conflicting","conflicting_and_collapsing",
                                    "first","look_ahead","random","recent_collapsing",
                                    "recent_conflicting","tightest_bound")),

  OptionName("color_unblocking","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("condensation","cond",GLOBAL_TAG,
             "If 'fast' is specified, we only perform condensations that are easy to check for.",
             false, "off", OptionValues("fast","off","on")),

  OptionName("decode","",GLOBAL_TAG,
             "",
             false),
  OptionName("demodulation_redundancy_check","drc",GLOBAL_TAG,
             "Avoids the following cases of backward and forward demodulation, as they do not preserve completeness:\n"
             "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n"
             "--------------------- \t ---------------------\n" 
             "t = t1 \\/ C \t\t t != t1 \\/ C\n"
             "where t > t1 and s = t > C (RHS replaced)",
             false, "true"),
  OptionName("distinct_processor","",GLOBAL_TAG,
             "handles $distinct predicates",
             false, "false"),

  OptionName("epr_preserving_naming","",GLOBAL_TAG,
             "Naming will not cause introduction of any non-constant functions.The nonconstant functions can be introduced by naming in a name definition when a universal quantifier turns into an existential one and is skolemized.",
             false, "false"),
  OptionName("epr_preserving_skolemization","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("epr_restoring_inlining","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("equality_propagation","",GLOBAL_TAG,
             "propagate equalities in formulas, for example\n"
             "X=Y => X=f(Y) ---> X=f(X)",
             false, "false"),
  OptionName("equality_proxy","ep",GLOBAL_TAG,
             "",
             false, "off", OptionValues("R","RS","RST","RSTC","off","on")),
  OptionName("equality_resolution_with_deletion","erd",GLOBAL_TAG,
             "",
             false, "input_only", OptionValues("input_only","off","on")),
  
  OptionName("extensionality_allow_pos_eq","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("extensionality_max_length","",GLOBAL_TAG,
             "",
             false, "0"),
  OptionName("extensionality_resolution","er",GLOBAL_TAG,
             "",
             false, "off",OptionValues("filter","known","off")),

  OptionName("flatten_top_level_conjunctions","",GLOBAL_TAG,
             "split formulas with top-level (up to universal quantification) conjunctions into several formulas",
             false, "false"),
  OptionName("forbidden_options","",GLOBAL_TAG,
             "strategies with specified option values will be skipped (not sure on format - check)",
             false), // no default
  OptionName("forced_options","",GLOBAL_TAG,
             "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the option values set by other means (also inside CASC mode strategies)",
             false), // no default
  OptionName("forward_demodulation","fd",GLOBAL_TAG,
             "Oriented rewriting of newly derived clauses by kept unit equalities\n"
             "s = t     L[sθ] \\/ C\n"
             "---------------------  where sθ > tθ\n"
             " L[tθ] \\/ C\n"
             "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.",
             false,"all", OptionValues("all","off","preordered")),
  OptionName("forward_literal_rewriting","flr",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("forward_subsumption","fs",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("forward_subsumption_resolution","fsr",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("function_definition_elimination","fde",GLOBAL_TAG,
             "",
             false, "all",OptionValues("all","none","unused")),
  OptionName("function_number","",GLOBAL_TAG,
             "",
             false, "1"),

  OptionName("general_splitting","gsp",GLOBAL_TAG,
             "Preprocessing rule that splits clauses in order to reduce number of different variables in each clause",
             false, "off",OptionValues("input_only","off","on")),
  OptionName("global_subsumption","gs",GLOBAL_TAG,
             "",
             false, "false"),

  OptionName("help","h",GLOBAL_TAG,
             "display this help",
             false,"off"),

  OptionName("horn_revealing","",GLOBAL_TAG,
             "Preprocessing rule that tries to discover whether polarities of predicates can be changed, so that problem becomes horn. If successful, marks all clauses with a positive literal as axioms, and those with only negatives as conjectures.",
             false, "false"),
  OptionName("hyper_superposition","",GLOBAL_TAG,
             "Generating inference that attempts to do several rewritings at once if it will eliminate literals of the original clause (now we aim just for elimination by equality resolution)",
             false, "false"),

  OptionName("ignore_missing","",GLOBAL_TAG,
             "Ignore any options that have been removed (useful in CASC mode where this can cause errors)",
             false, "false"),
  OptionName("include","",GLOBAL_TAG,
             "Path prefix for the 'include' TPTP directive",
             false, ""),
  OptionName("increased_numeral_weight","",GLOBAL_TAG,
             "weight of integer constants depends on the logarithm of their absolute value (instead of being 1)",
             false, "false"),
  OptionName("inequality_splitting","ins",GLOBAL_TAG,
             "",
             false, "3"),
  OptionName("input_file","",GLOBAL_TAG,
             "Problem file to be solved (if not specified, standard input is used)",
             false, ""),
  OptionName("input_syntax","",GLOBAL_TAG,
             "",
             false, 
//in case we compile vampire with bpa, then the default input syntax is smtlib
#if !GNUMP
             "tptp",
#else
             "smtlib",
#endif
             OptionValues("simplify","smtlib","smtlib2","tptp",
                          "xhuman","xmps","xnetlib")),
  OptionName("inst_gen_big_restart_ratio","igbrr",GLOBAL_TAG,
             "determines how often a big restart (instance generation starts from input clauses) will be performed. Small restart means all clauses generated so far are processed again.",
             false, "0.0"),
  OptionName("inst_gen_inprocessing","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("inst_gen_passive_reactivation","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("inst_gen_resolution_ratio","igrr",GLOBAL_TAG,
             "ratio of resolution and instantiation steps (applies only if inst_gen_with_resolution is on)",
             false, "1/1"),
  OptionName("inst_gen_restart_period","igrp",GLOBAL_TAG,
             "how many clauses are processed before (small?) restart",
             false, "1000"),
  OptionName("inst_gen_restart_period_quotient","igrpq",GLOBAL_TAG,
             "restart period is multiplied by this number after each restart",
             false, "1.0"),
  OptionName("inst_gen_selection","igs",GLOBAL_TAG,
             "selection function for InstGen. we don't have the functions 11 and 1011 yet (as it would need special treatment for the look-ahead)",
             false, "0"),
  OptionName("inst_gen_with_resolution","igwr",GLOBAL_TAG,
             "performs instantiation together with resolution (global subsuption index is shared, also clauses generated by the resolution are added to the instance SAT problem)",
             false, "false"),
  OptionName("interpreted_simplification","",GLOBAL_TAG,
             "Performs simplifications of interpreted functions. This option requires interpreted_evaluation to be enabled as well. IMPORTANT - Currently not supported",
             true, "false"),

  OptionName("latex_output","",GLOBAL_TAG,
             "File that will contain proof in the LaTeX format.",
             false, "off"),
  OptionName("lingva_additional_invariants","",GLOBAL_TAG,
             "",
             false, ""),

  OptionName("literal_comparison_mode","lcm",GLOBAL_TAG,
             "",
             false, "standard",OptionValues("predicate","reverse","standard")),
  OptionName("log_file","",GLOBAL_TAG,
             "",
             false, "off"),
  OptionName("lrs_first_time_check","",GLOBAL_TAG,
             "Percentage of time limit at which the LRS algorithm will for the first time estimate the number of reachable clauses.",
             false, "5"),
  OptionName("lrs_weight_limit_only","",GLOBAL_TAG,
             "If off, the lrs sets both age and weight limit according to clause reachability, otherwise it sets the age limit to 0 and only the weight limit reflects reachable clauses",
             false, "false"),

  OptionName("max_active","",GLOBAL_TAG,
             "",
             false, "0"),
  OptionName("max_answers","",GLOBAL_TAG,
             "",
             false, "1"),
  OptionName("max_inference_depth","",GLOBAL_TAG,
             "",
             false, "0"),
  OptionName("max_passive","",GLOBAL_TAG,
             "",
             false, "0"),
  OptionName("max_weight","",GLOBAL_TAG,
             "Weight limit for clauses (0 means no weight limit) (for lrs?)",
             false, "0"),
  OptionName("memory_limit","m",GLOBAL_TAG,
             "Memory limit in MB",
#if VDEBUG
             false, "1000"),
#else
             false, "3000"),
#endif
  OptionName("mode","",GLOBAL_TAG,
             "consequence_elimination mode forces values of unused_predicate_definition_removal and propositional_to_bdd to be off",
             false, "vampire",
                       OptionValues("axiom_selection","bpa","casc","casc_epr",
                                    "casc_ltb","casc_mzr","casc_sat","clausify",
                                    "consequence_elimination","grounding",
                                    "ltb_build","ltb_solve","output","preprocess",
                                    "profile","program_analysis","sat_solver",
                                    "spider","vampire")),

  OptionName("name_prefix","",GLOBAL_TAG,
             "Prefix for symbols introduced by Vampire (BDD-related propositional predicates, naming predicates, Skolem functions)",
             false, ""),
  OptionName("naming","nm",GLOBAL_TAG,
             "",
             false, "8"),
  OptionName("niceness_option","no",GLOBAL_TAG,
             "",
             true, "none",OptionValues("average","none","sum","top")),
  OptionName("nongoal_weight_coefficient","nwc",GLOBAL_TAG,
             "coefficient that will multiply the weight of theory clauses (those marked as 'axiom' in TPTP)",
             false, "1.0"),
  OptionName("nonliterals_in_clause_weight","nicw",GLOBAL_TAG,
             "Non-literal parts of clauses (such as BDDs or its split history) will also contribute to the weight",
             false, "false"),
  OptionName("normalize","",GLOBAL_TAG,
             "",
             false, "false"),

  OptionName("output_axiom_names","",GLOBAL_TAG,
             "preserve names of axioms from the problem file in the proof output",
             false, "false"),

  OptionName("predicate_definition_inlining","",GLOBAL_TAG,
             "non_growing rules out inlinings that would lead to increase in the size of the problem",
             false, "off",OptionValues("axioms_only","non_growwing","off","on")),
  OptionName("predicate_definition_merging","",GLOBAL_TAG,
             "Look for pairs of definitions such as"
             "p(X) <=> F[X]"
             "q(X) <=> F[X]"
             "replace the latter by"
             "q(X) <=> p(X)"
             "and use it to eliminate the predicate q(X).",
             false, "false"),
  OptionName("predicate_equivalence_discovery","",GLOBAL_TAG,
             "if enabled, SAT solver will be used to discover predicate equivalences during preprocessing. "
             "if all_atoms, equivalences between all atoms will be searched for. "
             "if definitions, we'll look only for equivalences in the shape of predicate definitions (this lies somewhere between on and all_atoms). "
             "if all_formulas, equivalences between all formulas are searched for",
             false, "off",OptionValues("all_atoms","all_formulas",
                                       "definitions","off","on")),
  OptionName("predicate_equivalence_discovery_add_implications","",GLOBAL_TAG,
             "if predicate_equivalence_discovery is enabled, add also discoveder implications, not only equivalences",
             false, "false"),
  OptionName("predicate_equivalence_discovery_random_simulation","",GLOBAL_TAG,
             "use random simulation before the simultaneous sat-sweeping to reduce the amount of candidate equivalences",
             false, "true"),
  OptionName("predicate_equivalence_discovery_sat_conflict_limit","",GLOBAL_TAG,
             "Limit on the number of SAT conflicts in each equivalence check. Default is -1 which stands for unlimited, 0 will restrict equivalence discovery to unit propagation. The implicative sat sweeping has an internal conflict count limit which always starts with zero and is increased geometrically until it reaches the limit set by this value",
             false, "-1"),
  OptionName("predicate_index_introduction","",GLOBAL_TAG,
             "If all atoms of a certain predicate contain distinct constants as a particular argument, atoms of the predicate"
             " are replaces by set of fresh predicates, one for each of the distinct constants.\n"
             "E.g. a problem\n"
             "p(a,b,X,1)\n"
             "p(a,c,a,2)\n"
             "will be transformed into\n"
             "p_a_1(b,X)\n"
             "p_a_2(c,a)\n"
             "(second argument is not removed because constants b and c are not necessarily distinct, and third argment is not replaced because it occurs as a variable)",
             false, "false"),
  OptionName("print_clausifier_premises","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("problem_name","",GLOBAL_TAG,
             "",
             false),
  OptionName("proof","p",GLOBAL_TAG,
             "Specifies whether proof will be output. 'proofcheck' will output proof as a sequence of TPTP problems to allow for proof-checking.",
             false, "on",OptionValues("off","on","proofcheck","tptp")),
  OptionName("proof_checking","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("protected_prefix","",GLOBAL_TAG,
             "symbols with this prefix are immune against elimination during preprocessing",
             false, ""),

  OptionName("question_answering","",GLOBAL_TAG,
             "",
             false, "off",OptionValues("answer_literal","from_proof","off")),

  OptionName("random_seed","",GLOBAL_TAG,
             "",
             false), // special case - set in constructor 
  OptionName("row_variable_max_length","",GLOBAL_TAG,
             "",
             false, "2"),

  OptionName("sat_clause_activity_decay","",GLOBAL_TAG,
             "",
             false, "1.001"),
  OptionName("sat_clause_disposer","",GLOBAL_TAG,
             "",
             false, "minisat",OptionValues("growing","minisat")),
  OptionName("sat_learnt_minimization","",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("sat_learnt_subsumption_resolution","",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("sat_restart_fixed_count","",GLOBAL_TAG,
             "",
             false, "16000"),
  OptionName("sat_restart_geometric_increase","",GLOBAL_TAG,
             "",
             false, "1.1"),
  OptionName("sat_restart_geometric_init","",GLOBAL_TAG,
             "",
             false, "32"),
  OptionName("sat_restart_luby_factor","",GLOBAL_TAG,
             "",
             false, "100"),
  OptionName("sat_restart_minisat_increase","",GLOBAL_TAG,
             "",
             false, "1.1"),
  OptionName("sat_restart_minisat_init","",GLOBAL_TAG,
             "",
             false, "100"),
  OptionName("sat_restart_strategy","",GLOBAL_TAG,
             "",
             false, "luby",OptionValues("fixed","geometric","luby","minisat")),
  OptionName("sat_solver","sas",VAMPIRE_TAG,
             "Select the SAT solver to be used throughout the solver. This will be used in AVATAR (for splitting) when the saturation algorithm is discount,lrs or otter and in instance generation for selection and global subsumption. The buf options are experimental (they add buffering).",
             false, "vampire",OptionValues("buf_lingeling","buf_vampire",
                                           "lingeling","vampire")),
  OptionName("sat_var_activity_decay","",GLOBAL_TAG,
             "",
             false, "1.05"),
  OptionName("sat_var_selector","svs",GLOBAL_TAG,
             "",
             false, "active",OptionValues("active","niceness","recently_learnt")),
  OptionName("saturation_algorithm","sa",GLOBAL_TAG,
             "inst_gen and tabulation aren't influenced by options for the saturation algorithm, apart from those mentioned. tabulation is a special goal-oriented mode for large theories. inst_gen is a simple implementation of instantiation calculus - global_subsumption, unit_resulting_resolution and age_weight_ratio are supported",
             false, "lrs",OptionValues("discount","inst_gen","lrs",
                                       "otter","tabulation")),
  OptionName("selection","s",GLOBAL_TAG,
             "",
             false, "10"),
  OptionName("show_active","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_blocked","",GLOBAL_TAG,
             "show generating inferences blocked due to coloring of symbols",
             false, "false"),
  OptionName("show_definitions","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_experimental_options","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_interpolant","",GLOBAL_TAG,
             "minimized tries to find a nicer interpolant than the default algorithm does",
             false, "off",OptionValues("minimized","off","on")),
  OptionName("show_new","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_new_propositional","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_nonconstant_skolem_function_trace","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_options","",GLOBAL_TAG,
             "",
             false, "off",OptionValues("bp","off","on","vampire")),
  OptionName("show_passive","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_preprocessing","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_skolemisations","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_symbol_elimination","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("show_theory_axioms","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("simulated_time_limit","stl",GLOBAL_TAG,
             "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)",
             false, "0"),
  OptionName("sine_depth","sd",GLOBAL_TAG,
             "Limit number of iterations of the transitive closure algorithm that selects formulas based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal limit (least selected axioms), 2 allows two iterations, etc...",
             false, "0"),
  OptionName("sine_generality_threshold","sgt",GLOBAL_TAG,
             "Generality of a symbol is the number of input formulas in which a symbol appears. If the generality of a symbol is smaller than the threshold, it is always added into the D-relation with formulas in which it appears.",
             false, "0"),
  OptionName("sine_selection","ss",GLOBAL_TAG,
             "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) are initially selected, and the SInE selection is performed on those annotated as 'axiom'. If 'included', all formulas that are directly in the problem file are initially selected, and the SInE selection is performed on formulas from included files. The 'included' value corresponds to the behaviour of the original SInE implementation.",
             false, "off",OptionValues("axioms","included","off")),
  OptionName("sine_tolerance","st",GLOBAL_TAG,
             "SInE tolerance parameter (sometimes referred to as 'benevolence')",
             false, "1.0"),
  OptionName("smtlib_consider_ints_real","",GLOBAL_TAG,
             "all integers will be considered to be reals by the SMTLIB parser",
             false, "false"),
  OptionName("smtlib_flet_as_definition","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("smtlib_introduce_aig_names","",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("sos","sos",GLOBAL_TAG,
             "Set of support strategy. All formulas annotated as theory axioms are put directly among active clauses, without performing any inferences between them. If all, select all literals of set-of-support clauses, ortherwise use the default literal selector.",
             false, "off",OptionValues("all","off","on")),
  OptionName("split_at_activation","sac",GLOBAL_TAG,
             "",
             false, "false"), //check if valid option
  OptionName("splitting","spl",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("ssplitting_add_complementary","ssac",GLOBAL_TAG,
             "",
             true, "ground",OptionValues("ground","none")),
  OptionName("ssplitting_component_sweeping","",GLOBAL_TAG,
             "The idea of component selection is described at the top of SSplitter.hpp. The meaning of options is: none .. no sweeping is done. only_new .. after each SAT model update we do sweeping on the newly selected components. all .. after each SAT model update we do sweeping on all selected components iterated .. like all except that we repeat the sweping while some components are being deselected",
             true, "iterated",OptionValues("all","iterated","none","only_new")),
  OptionName("ssplitting_congruence_closure","sscc",GLOBAL_TAG,
             "",
             true, "false"),
  OptionName("ssplitting_eager_removal","sser",GLOBAL_TAG,
             "",
             true, "true"),
  OptionName("ssplitting_flush_period","ssfp",GLOBAL_TAG,
             "after given number of generated clauses without deriving an empty clause, the splitting component selection is shuffled. If equal to zero, shuffling is never performed.",
             true, "0"),
  OptionName("ssplitting_flush_quotient","ssfq",GLOBAL_TAG,
             "after each flush, the ssplitting_flush_period is multiplied by the quotient",
             true, "1.5"),
  OptionName("ssplitting_nonsplittable_components","ssnc",GLOBAL_TAG,
             "known .. SAT clauses will be learnt from non-splittable clauses that have corresponding components (if there is a component C with name SAT l, clause C | {l1,..ln} will give SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original FO clause C | {l1,..ln} and let the component selection update model, possibly adding the component clause C | {l}. all .. like known, except when we see a non-splittable clause that doesn't have a name, we introduce the name for it. all_dependent .. like all, but we don't introduce names for non-splittable clauses that don't depend on any components",
             true, "known",OptionValues("all","all_dependent","known","none")),
  OptionName("statistics","",GLOBAL_TAG,
             "",
             false, "full", OptionValues("brief","full","none")),
  OptionName("superposition_from_variables","sfv",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("symbol_precedence","sp",GLOBAL_TAG,
             "",
             false, "arity",OptionValues("arity","occurrence","reverse_arity")),

  OptionName("tabulation_bw_rule_subsumption_resolution_by_lemmas","tbsr",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("tabulation_fw_rule_subsumption_resolution_by_lemmas","tfsr",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("tabulation_goal_awr","tgawr",GLOBAL_TAG,
             "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next goal clause to process",
             false, "1/1"), 
  OptionName("tabulation_goal_lemma_ratio","tglr",GLOBAL_TAG,
             "when saturation algorithm is set to tabulation, this option determines the ratio of processing new goals and lemmas",
             false, "1/1"),
  OptionName("tabulation_instantiate_producing_rules","tipr",GLOBAL_TAG,
             "when saturation algorithm is set to tabulation, this option determines whether the producing rules will be made of theory clauses (in case it's off), or of their instances got from the substitution unifying them with the goal",
             false, "true"),
  OptionName("tabulation_lemma_awr","tlawr",GLOBAL_TAG,
             "when saturation algorithm is set to tabulation, this option determines the age-weight ratio for selecting next lemma to process",
             false, "1/1"), 
  OptionName("test_id","",GLOBAL_TAG,
             "",
             false, "unspecified_test"),
  OptionName("thanks","",GLOBAL_TAG,
             "",
             false, "Tanya"),
  OptionName("theory_axioms","",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("time_limit","t",GLOBAL_TAG,
             "Time limit in wall clock seconds",
             false, "600"),
  OptionName("time_statistics","",GLOBAL_TAG,
             "Show how much running time was spent in each part of the Vampire",
             false, "false"),
  OptionName("trivial_predicate_removal","",GLOBAL_TAG,
             "remove predicates never occurring only positively or only negatively in a clause",
             false, "false"),

  OptionName("unit_resulting_resolution","urr",GLOBAL_TAG,
             "uses unit resulting resolution only to derive empty clauses (may be useful for splitting)",
             false, "off",OptionValues("ec_only","off","on")),
  OptionName("unused_predicate_definition_removal","updr",GLOBAL_TAG,
             "",
             false, "true"),
  OptionName("use_dismatching","",GLOBAL_TAG,
             "",
             false, "false"),

  OptionName("weight_increment","",GLOBAL_TAG,
             "",
             false, "false"),
  OptionName("while_number","",GLOBAL_TAG,
             "",
             false, "1"),

  OptionName("xml_output","",GLOBAL_TAG,
             "",
             false, "off")
  };
>>>>>>> Add OptionNameArray and use it in Shell/Options

/** Names for all options */
OptionNameArray Options::Constants::optionNames(_optionNames,
		  sizeof(_optionNames)/sizeof(OptionName));



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

  // necessary to set here as it uses a function call
  _randomSeed(Random::seed()),

  // not sure where these are set or what they control
  _selectUnusedVariablesFirst(false),
  _updatesByOneConstraint(3)

{
  CALL("Options::Options");

  //Set the default values
  for(int i=0;i<Constants::optionNames.length;i++){
        const char* default_value = Constants::optionNames[i].default_value;
        const char* longName = Constants::optionNames[i].longName;
        if(default_value){
	  set(longName,default_value, i); 
        }
  }

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
      _backwardDemodulation = (Demodulation)Constants::optionNames[BACKWARD_DEMODULATION].names->find(value);
      return;
    case BACKWARD_SUBSUMPTION:
      _backwardSubsumption = (Subsumption)Constants::optionNames[BACKWARD_SUBSUMPTION].names->find(value);
      return;
    case BACKWARD_SUBSUMPTION_RESOLUTION:
      _backwardSubsumptionResolution = (Subsumption)Constants::optionNames[BACKWARD_SUBSUMPTION_RESOLUTION].names->find(value);
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
      _bpAlmostHalfBoundingRemoval = (BPAlmostHalfBoundingRemoval)Constants::optionNames[BP_ALMOST_HALF_BOUND_REMOVER].names->find(value);
      return;
    case BP_ASSIGNMENT_SELECTOR:
      _bpAssignmentSelector = (BPAssignmentSelector)Constants::optionNames[BP_ASSIGNMENT_SELECTOR].names->find(value);
      return;
    case BP_COLLAPSING_PROPAGATION:
      _bpCollapsingPropagation = onOffToBool(value,name);
      return;
    case BP_CONFLICT_SELECTOR:
      _bpConflictSelector = (BPConflictSelector)Constants::optionNames[BP_CONFLICT_SELECTOR].names->find(value);
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
      _bpVariableSelector = (BPVariableSelector)Constants::optionNames[BP_VARIABLE_SELECTOR].names->find(value);
      return;

    case COLOR_UNBLOCKING:
      _colorUnblocking = onOffToBool(value,name);
      return;
    case CONDENSATION:
      _condensation =
	(Condensation)Constants::optionNames[CONDENSATION].names->find(value);
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
      _equalityProxy = (EqualityProxy)Constants::optionNames[EQUALITY_PROXY].names->find(value);
      return;
    case EQUALITY_RESOLUTION_WITH_DELETION:
      _equalityResolutionWithDeletion = (RuleActivity)Constants::optionNames[EQUALITY_RESOLUTION_WITH_DELETION].names->find(value);
      if (_equalityResolutionWithDeletion==RA_ON) {
	USER_ERROR("equality_resolution_with_deletion is not implemented for value \"on\"");
      }
      return;
    case EXTENSIONALITY_RESOLUTION:
      _extensionalityResolution = (ExtensionalityResolution)Constants::optionNames[EXTENSIONALITY_RESOLUTION].names->find(value);
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
	(Demodulation)Constants::optionNames[FORWARD_DEMODULATION].names->find(value);
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
	(FunctionDefinitionElimination)Constants::optionNames[FUNCTION_DEFINITION_ELIMINATION].names->find(value);
      return;
    case FUNCTION_NUMBER:
      if (Int::stringToInt(value,intValue))
    	  _functionNumber= intValue;
      return;

    case GENERAL_SPLITTING:
      _generalSplitting = (RuleActivity)Constants::optionNames[GENERAL_SPLITTING].names->find(value);
      if (_generalSplitting==RA_ON) {
	USER_ERROR("general_splitting is not implemented for value \"on\"");
      }
      return;
    case GLOBAL_SUBSUMPTION:
      _globalSubsumption = onOffToBool(value,name);
      return;

    case HELP:
      _showHelp = onOffToBool(value,name);
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
      _inputSyntax = (InputSyntax)Constants::optionNames[INPUT_SYNTAX].names->find(value);
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
	(LiteralComparisonMode)Constants::optionNames[LITERAL_COMPARISON_MODE].names->find(value);
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
      _mode = (Mode)Constants::optionNames[MODE].names->find(value);
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
      _predicateDefinitionInlining = (InliningMode)Constants::optionNames[PREDICATE_DEFINITION_INLINING].names->find(value);
      return;
    case PREDICATE_DEFINITION_MERGING:
      _predicateDefinitionMerging = onOffToBool(value,name);
      return;
    case PREDICATE_EQUIVALENCE_DISCOVERY:
      _predicateEquivalenceDiscovery =
	  (PredicateEquivalenceDiscoveryMode)Constants::optionNames[PREDICATE_EQUIVALENCE_DISCOVERY].names->find(value);
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
      _proof = (Proof)Constants::optionNames[PROOF].names->find(value);
      return;
    case PROOF_CHECKING:
      _proofChecking = onOffToBool(value,name);
      return;
    case PROTECTED_PREFIX:
      _protectedPrefix = value;
      return;

    case QUESTION_ANSWERING:
      _questionAnswering = (QuestionAnsweringMode)Constants::optionNames[QUESTION_ANSWERING].names->find(value);
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
      _satClauseDisposer = (SatClauseDisposer)Constants::optionNames[SAT_CLAUSE_DISPOSER].names->find(value);
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
      _satRestartStrategy = (SatRestartStrategy)Constants::optionNames[SAT_RESTART_STRATEGY].names->find(value);
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
      _satVarSelector = (SatVarSelector)Constants::optionNames[SAT_VAR_SELECTOR].names->find(value);
      return;
    case NICENESS_OPTION:
      _nicenessOption = (NicenessOption)Constants::optionNames[NICENESS_OPTION].names->find(value);
      return;
    case SAT_SOLVER:
      _satSolver = (SatSolver) Constants::optionNames[SAT_SOLVER].names->find(value);
      return;
    case SATURATION_ALGORITHM:
      _saturationAlgorithm = (SaturationAlgorithm)Constants::optionNames[SATURATION_ALGORITHM].names->find(value);
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
    case SHOW_EXPERIMENTAL_OPTIONS:
      _showExperimentalOptions = onOffToBool(value,name);
      return;
    case SHOW_INTERPOLANT:
      _showInterpolant = (InterpolantMode)Constants::optionNames[SHOW_INTERPOLANT].names->find(value);
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
      _showOptions = (OptionTag) Constants::optionNames[SHOW_OPTIONS].names->find(value);
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
	(SineSelection)Constants::optionNames[SINE_SELECTION].names->find(value);
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
      _sos = (Sos)Constants::optionNames[SOS].names->find(value);
      return;
    case SPLIT_AT_ACTIVATION:
      _splitAtActivation = onOffToBool(value,name);
      return;
    case SPLITTING:
      _splitting = onOffToBool(value,name);
      return;
    case SSPLITTING_ADD_COMPLEMENTARY:
      _ssplittingAddComplementary = (SSplittingAddComplementary)Constants::optionNames[SSPLITTING_ADD_COMPLEMENTARY].names->find(value);
      return;
    case SSPLITTING_COMPONENT_SWEEPING:
      _ssplittingComponentSweeping = (SSplittingComponentSweeping)Constants::optionNames[SSPLITTING_COMPONENT_SWEEPING].names->find(value);
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
      _ssplittingNonsplittableComponents = (SSplittingNonsplittableComponents)Constants::optionNames[SSPLITTING_NONSPLITTABLE_COMPONENTS].names->find(value);
      return;
      
    case STATISTICS:
      _statistics = (Statistics) Constants::optionNames[STATISTICS].names->find(value);
      return;
    case SUPERPOSITION_FROM_VARIABLES:
      _superpositionFromVariables = onOffToBool(value,name);
      return;
    case SYMBOL_PRECEDENCE:
      _symbolPrecedence =
	(SymbolPrecedence)Constants::optionNames[SYMBOL_PRECEDENCE].names->find(value);
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
    case TIME_STATISTICS:
      _timeStatistics = onOffToBool(value,name);
      return;
    case TRIVIAL_PREDICATE_REMOVAL:
      _trivialPredicateRemoval = onOffToBool(value,name);
      return;

    case UNIT_RESULTING_RESOLUTION:
      _unitResultingResolution = (URResolution)Constants::optionNames[UNIT_RESULTING_RESOLUTION].names->find(value);
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
