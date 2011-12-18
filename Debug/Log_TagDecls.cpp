/**
 * @file Log_TagDecls.cpp
 * Implements class Log_TagDecls.
 */

#include "Log.hpp"

#if LOGGING

#include "Log_TagDecls.hpp"

namespace Debug
{

void Logging::doTagDeclarations()
{
  DECL("active_clauses",
      DOC("displays active clauses"));
  DECL("passive_clauses",
      DOC("displays passive clauses"));
  DECL("unprocessed_clauses",
      DOC("displays unprocessed clauses"));
  DECL("new_clauses",
      DOC("displays newly derived clauses"));
  DECL("new_prop_clauses",
      DOC("displays newly derived propositional clauses"));

  DECL("preproc_forms",
      DOC("prints clauses after preprocessing, just before they are put into the main loop"));

  DECL("definitions");

  DECL("ls",
      DOC("literal selection"));

  DECL("arith",
      DOC("arithmetic related traces"));

  //
  // SaturationAlgorithm
  //

  DECL("sa",
      DOC("traces related to saturation algorithm"));

  DECL("sa_containers",
      DOC("traces related saturation algorithm containers"),
      PARENT("sa", 1));

  DECL("splitting_definition",
      PARENT("definitions", 0));

  DECL("sa_active_added",
      PARENT("active_clauses", 0),
      PARENT("sa_containers", 0));
  DECL("sa_passive_added",
      PARENT("passive_clauses", 0),
      PARENT("sa_containers", 0));
  DECL("sa_unprocessed_added",
      PARENT("unprocessed_clauses", 0),
      PARENT("sa_containers", 0));

  DECL("sa_active_removed",
      PARENT("sa_containers", 0));
  DECL("sa_passive_removed",
      PARENT("sa_containers", 0));
  DECL("sa_unprocessed_removed",
      PARENT("sa_containers", 0));
  DECL("sa_reanimated",
      PARENT("sa_containers", 0));
  DECL("sa_passive_selected",
      PARENT("sa_containers", 0));
  DECL("sa_unprocessed_selected",
      PARENT("sa_containers", 0));


  DECL("sa_new_clause",
      PARENT("new_clauses", 0),
      PARENT("sa", 1));
  DECL("sa_new_prop_clause",
      DOC("new propositional clause derived by the saturation algorithm"),
      PARENT("sa_new_clause", 1),
      PARENT("new_prop_clauses", 0));

  DECL("sa_generated_clause",
      DOC("clause derived by generating inference"),
      PARENT("sa", 1));
  DECL("sa_retained_clause",
      DOC("clause passed forward simplification checks"),
      PARENT("sa", 1));

  DECL("sa_simpl",
      DOC("simplifications in saturation algorithm"),
      PARENT("sa", 1));

  DECL("sa_fw_simpl",
      DOC("forward simplifications in saturation algorithm"),
      PARENT("sa_simpl", 0));
  DECL("sa_bw_simpl",
      DOC("backward simplifications in saturation algorithm"),
      PARENT("sa_simpl", 0));


  //
  // IGAlgorithm
  //

  DECL("ig",
      DOC("traces related to inst-gen algorithm"));

  DECL("ig_restarts",
      DOC("traces restarts of inst-gen algorithm"),
      PARENT("ig", 0));

  DECL("ig_containers",
      DOC("traces related inst-gen algorithm containers"),
      PARENT("ig", 1));

  DECL("ig_active_added",
      PARENT("active_clauses", 0),
      PARENT("ig_containers", 0));
  DECL("ig_passive_added",
      PARENT("passive_clauses", 0),
      PARENT("ig_containers", 0));
  DECL("ig_unprocessed_added",
      PARENT("unprocessed_clauses", 0),
      PARENT("ig_containers", 0));


  DECL("ig_new_clause",
      PARENT("new_clauses", 0),
      PARENT("ig", 1));

  DECL("ig_sat",
      DOC("traces calls to the SAT solver from inst-gen"),
      PARENT("ig", 1));
  DECL("ig_literal_selection",
      PARENT("ig", 1),
      PARENT("ls", 0));
  DECL("ig_mdl",
      DOC("model generation for inst-gen"),
      PARENT("ig", 1));


  //
  // Inferences
  //

  DECL("inf",
      DOC("inferences"));

  DECL("inf_fwd",
      DOC("forward demodulation"),
      PARENT("inf",1));
  DECL("inf_fwd_tlcheck",
      DOC("top-level check in forward demodulation"),
      PARENT("inf_fwd",1));

  DECL("inf_bsr",
      DOC("backward subsumption resolution"),
      PARENT("inf",1));

  DECL("inf_cond",
      DOC("condensation"),
      PARENT("inf",1));
  DECL("inf_cond_reg",
      DOC("regular condensation"),
      PARENT("inf_cond",0));
  DECL("inf_cond_fast",
      DOC("fast condensation"),
      PARENT("inf_cond",0));

  DECL("inf_des",
      DOC("distinct equality simplifier"),
      PARENT("inf",1));

  DECL("inf_gs",
      DOC("global subsumption"),
      PARENT("inf",1));

  DECL("inf_flr",
      DOC("forward literal rewriting"),
      PARENT("inf",1));
  DECL("inf_flr_defs",
      DOC("discovered definitions"),
      PARENT("inf_flr",1));

  DECL("inf_ie",
      DOC("interpreted evaluation"),
      PARENT("inf",1),
      PARENT("arith",1));


  //
  // SAT-based splitting
  //

  DECL("sspl",
      DOC("traces for SAT-based splitting"));
  DECL("sspl_splits",
      DOC("performed splits"),
      PARENT("sspl",0));
  DECL("sspl_nonsplits",
      DOC("not splitted clauses"),
      PARENT("sspl",3));
  DECL("sspl_confl",
      DOC("SAT conflict clauses generated"),
      PARENT("sspl",0));
  DECL("sspl_confl_derivations",
      DOC("output derivations of SAT conflict clauses"),
      PARENT("sspl_confl",1));
  DECL("sspl_comp_names",
      DOC("introduced component names"),
      PARENT("sspl",1));
  DECL("sspl_flush",
      DOC("flushing"),
      PARENT("sspl",0));

  DECL("sspl_sel",
      DOC("component selection"),
      PARENT("sspl",1));
  DECL("sspl_sel_added",
      DOC("components added to selection"),
      PARENT("sspl_sel",0));
  DECL("sspl_sel_removed",
      DOC("components removed from selection"),
      PARENT("sspl_sel",0));
  DECL("sspl_sel_current_comps",
      DOC("list of currently selected components"),
      PARENT("sspl_sel",1));
  DECL("sspl_sel_swept",
      DOC("swept components"),
      PARENT("sspl_sel",2));


  DECL("sspl_rm",
      DOC("level removals upon change of component selection"),
      PARENT("sspl",2));
  DECL("sspl_rm_backtracked",
      DOC("clause removals due to backtracking upon change of component selection"),
      PARENT("sspl_rm",1));
  DECL("sspl_rm_restored",
      DOC("restored claused due to backtracking upon change of component selection"),
      PARENT("sspl_rm",1));

  DECL("sspl_reductions",
      DOC("recording of clause reductions"),
      PARENT("sspl",3));
  DECL("sspl_reductions_prems",
      DOC("recording of clause reduction premises"),
      PARENT("sspl_reductions",3));
  DECL("sspl_new_cl_levels",
      DOC("levels assigned to new clauses"),
      PARENT("sspl",3));

  DECL("sspl_var_cnt",
      PARENT("sspl",4));

  DECL("sspl_sat_clauses",
      DOC("all clauses added to SAT solver"),
      PARENT("sspl",4));

  DECL("sspl_paired_gnd_comps",
      DOC("paired ground components"),
      PARENT("sspl",2));


  DECL("sspl_ns",
      DOC("processing of non-splittable FO clauses"),
      PARENT("sspl",1));
  DECL("sspl_ns_sat_clauses",
      DOC("recording of sat clauses added based on non-splittable FO clauses"),
      PARENT("sspl_ns",0));
  DECL("sspl_ns_self_dependent",
      DOC("clause that depends on a component that is its variant"),
      PARENT("sspl_ns",0));

  //
  // Preprocessing
  //

  DECL("pp",
      DOC("preprocessing traces"));

  DECL("pp_sk",
      DOC("solemization"),
      PARENT("pp",1));
  DECL("pp_sk_funs",
      DOC("introduced skolem functions"),
      PARENT("pp_sk",0));
  DECL("pp_sk_nonconst_intr",
      DOC("trace introductions of non-constant skolem functions"),
      PARENT("pp_sk",0));

  DECL("pp_pre_cl",
      DOC("print-out the problem just before clausification"),
      PARENT("pp",1));

  DECL("pp_pre_ennf",
      DOC("print-out the problem just before conversion to ennf"),
      PARENT("pp",1));

  DECL("pp_esk",
      DOC("epr-restoring skolemization"),
      PARENT("pp",1));
  DECL("pp_esk_inst",
      DOC("predicate instances detected during epr-restoring skolemization"),
      PARENT("pp_esk",1));
  DECL("pp_esk_contst",
      DOC("skolem constants introduced by epr-restoring skolemization"),
      PARENT("pp_esk",1));
  DECL("pp_esk_quant",
      DOC("quantifier processing in epr-restoring skolemization"),
      PARENT("pp_esk",1));

  DECL("pp_hr",
      DOC("horn revealer"),
      PARENT("pp",1));

  DECL("pp_inl",
      DOC("predicate definition inlining"),
      PARENT("pp",1));
  DECL("pp_inl_def",
      DOC("definition added"),
      PARENT("pp_inl",1));
  DECL("pp_inl_scan",
      DOC("scanning for definitions"),
      PARENT("pp_inl",1));
  DECL("pp_inl_step",
      DOC("inlining step"),
      PARENT("pp_inl",1));
  DECL("pp_inl_substep",
      DOC("inlining substeps"),
      PARENT("pp_inl_step",1));
  DECL("pp_inl_dep",
      DOC("tracing dependencies between predicates"),
      PARENT("pp_inl",1));

  DECL("pp_pdm",
      DOC("predicate definition merging"),
      PARENT("pp",1));

  DECL("pp_updr",
      DOC("unused predicate definition removal and pure predicate removal"),
      PARENT("pp",1));
  DECL("pp_updr_counts",
      DOC("predicate counts in updr"),
      PARENT("pp_updr",1));

  DECL("pp_tpr",
      DOC("trivial predicate remover"),
      PARENT("pp",1));

  DECL("pp_ea",
      DOC("equality_axiomatizer"),
      PARENT("pp",1));

  DECL("pp_ed",
      DOC("equivalence discovery"),
      PARENT("pp",1));
  DECL("pp_ed_progress",
      DOC("progress of the equivalence discovery algorithm"),
      PARENT("pp_ed",0));
  DECL("pp_ed_eq",
      DOC("discovered equivalences"),
      PARENT("pp_ed",0));
  DECL("pp_ed_asm",
      DOC("assumptions being asserted into the solver"),
      PARENT("pp_ed",1));

  DECL("pp_aig",
      DOC("aig sub-formula sharing"),
      PARENT("pp",1));
  DECL("pp_aig_transf",
      DOC("formulas transformed by aig sharing"),
      PARENT("pp_aig",0));
  DECL("pp_aig_sharing",
      DOC("aig introduced sub-formula sharing"),
      PARENT("pp_aig",1));
  DECL("pp_aig_nodes",
      DOC("nodes assigned to formulas by AIG"),
      PARENT("pp_aig",1));
  DECL("pp_aig_subformula_nodes",
      DOC("nodes assigned to subformulas by AIG"),
      PARENT("pp_aig_nodes",1));
  DECL("pp_aig_junction_building",
      DOC("progress of building junction AIGs"),
      PARENT("pp_aig_subformula_nodes",1));

  //
  // BFNT
  //

  DECL("bfnt");

  DECL("bfnt_cl",
      DOC("clauses generated by bfnt"),
      PARENT("bfnt",1));
  DECL("bfnt_cl_ineq",
      DOC("bfnt clauses expressing inequalities between constants"),
      PARENT("bfnt_cl",0));
  DECL("bfnt_cl_tot",
      DOC("bfnt clauses expressing totality of functions"),
      PARENT("bfnt_cl",0));
  DECL("bfnt_cl_transf",
      DOC("problem clauses transformed to bfnt"),
      PARENT("bfnt_cl",0));

  DECL("bfnt_loop",
      DOC("bfnt solving loop"),
      PARENT("bfnt",1));

  //
  // Interpolation
  //

  DECL("itp",
      DOC("interpolation traces"));

  DECL("itp_min",
      DOC("interpolant minimizer"),
      PARENT("itp",1));


  //
  // SAT solver
  //

  DECL("sat",
      DOC("SAT solver traces"));

  DECL("sat_clauses",
      DOC("added clauses"));

  DECL("sat_asmp",
      DOC("SAT solver assumptions"),
      PARENT("sat",0));

  DECL("sat_levels",
      DOC("decisions and backtracking in SAT solver"),
      PARENT("sat",1));

  DECL("sat_learnt",
      DOC("learnt clauses in SAT solver"),
      PARENT("sat",1));
  DECL("sat_learnt_gen",
      DOC("generating of learnt clauses in SAT solver"),
      PARENT("sat_learnt",1));
  DECL("sat_learnt_prems",
      DOC("premises of learnt clauses in SAT solver (shows all premises only when proof generation is enabled in SAT solver)"),
      PARENT("sat_learnt",1));

  DECL("sat_ts",
      DOC("transparent sat preprocessor"),
      PARENT("sat",0));
  DECL("sat_ts_pure",
      DOC("pure variables"),
      PARENT("sat_ts",1));
  DECL("sat_ts_in",
      DOC("clauses and assumptions added"),
      PARENT("sat_ts",1));
  DECL("sat_ts_out",
      DOC("clauses and assumptions passed to the inner solver"),
      PARENT("sat_ts",1));

  //
  // Multiprocessing
  //

  DECL("mp",
      DOC("tracing of multiprocessing features"));

  DECL("mp_sem",
      DOC("tracing of semaphores"),
      PARENT("mp",1));

  DECL("mp_wait",
      DOC("waiting for child processes"),
      PARENT("mp",1));


  //
  // Api
  //

  DECL("api",
      DOC("traces related to Vampire API"));
  DECL("api_prb",
      DOC("traces related to Vampire API for problems"));
  DECL("api_prb_transf",
      DOC("traces related to Vampire API problem transformations"));

  //
  // Other
  //

  DECL("test_tag",
      DOC("trace tag to be used for testing"));

  DECL("bdd");
  DECL("bdd_clausifier",
      PARENT("bdd",1));

  DECL("kbo");
  DECL("kbo_prec",
      PARENT("kbo",0));

  DECL("tab",
      DOC("tabulation"));

  DECL("ls_lookahead",
      DOC("look-ahead literal selection function (fn number 11)"),
      PARENT("ls",1));

  DECL("match_oc",
      DOC("matching code with occurs_check"));

  DECL("ord_diff",
      DOC("diff between results of two ordering algrithms (must be explicitly used in code)"));

  DECL("srt_collect_var_sorts",
      DOC("code for collecting variable sorts from terms and formulas"));

  DECL("arith_num_parsing",
      PARENT("arith",1));
  DECL("arith_axioms",
      DOC("theory axiom loader traces"),
      PARENT("arith",0));

  DECL("st",
      DOC("substitution trees"));
  DECL("st_fast_inst",
      DOC("fast instance retrieval in substitution trees"),
      PARENT("st",1));

  DECL("ae",
      DOC("answer extraction"));

  DECL("simplify",
      DOC("simplify prover traces"));

  DECL("smt_interface",
      DOC("traces from interface to SMT solver"));

  DECL("vu_z3ie",
      DOC("traces from z3 interpolant extractor"));
  DECL("vu_ers",
      DOC("traces from epr restoring scanner"));

  DECL("ut",
      DOC("traces in the unit-testing infrastructure"));
  DECL("ut_forking",
      PARENT("ut",1));

  DECL("prb",
      DOC("Object Kernel::Problem"));
  DECL("prb_prop_refresh",
      DOC("logs when property of a problem needs to be updated by traversing through the problem"),
      PARENT("prb",0));

  DECL("tu",
      DOC("TestUtils traces"));
  DECL("tu_uf",
      DOC("TestUtils::getUniqueFormula"),
      PARENT("tu",1));
}


}

#endif
