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
  DECL("bug",
      DOC("this tag is always enabled, bugs are to be reported through it or its children"));

  DECL("stat_labels",
      DOC("labels of statistics to be output, printed in the order in which they appeared on the command line"));

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
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_passive_added",
      PARENT("passive_clauses", 0),
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_unprocessed_added",
      PARENT("unprocessed_clauses", 0),
      PARENT("sa_containers", 0),
      UNIT_TAG);

  DECL("sa_active_removed",
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_passive_removed",
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_unprocessed_removed",
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_reanimated",
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_passive_selected",
      PARENT("sa_containers", 0),
      UNIT_TAG);
  DECL("sa_unprocessed_selected",
      PARENT("sa_containers", 0),
      UNIT_TAG);


  DECL("sa_new_clause",
      PARENT("new_clauses", 0),
      PARENT("sa", 1),
      UNIT_TAG);
  DECL("sa_new_prop_clause",
      DOC("new propositional clause derived by the saturation algorithm"),
      PARENT("sa_new_clause", 1),
      PARENT("new_prop_clauses", 0),
      UNIT_TAG);

  DECL("sa_generated_clause",
      DOC("clause derived by generating inference"),
      PARENT("sa", 1),
      UNIT_TAG);
  DECL("sa_retained_clause",
      DOC("clause passed forward simplification checks"),
      PARENT("sa", 1));

  DECL("sa_simpl",
      DOC("simplifications in saturation algorithm"),
      PARENT("sa", 1));

  DECL("sa_fw_simpl",
      DOC("forward simplifications in saturation algorithm"),
      PARENT("sa_simpl", 0));
  DECL("sa_fw_simpl_red_clause",
      DOC("clauses shown redundant by forward simplifications"),
      PARENT("sa_fw_simpl", 0),
      UNIT_TAG);
  DECL("sa_bw_simpl",
      DOC("backward simplifications in saturation algorithm"),
      PARENT("sa_simpl", 0));
  DECL("sa_bw_simpl_red_clause",
      DOC("clauses shown redundant by backward simplifications"),
      PARENT("sa_bw_simpl", 0),
      UNIT_TAG);

  DECL("sa_lrs",
      PARENT("sa", 1));
  DECL("sa_lrs_limit_weight",
      PARENT("sa_lrs", 1),
      INT_TAG);
  DECL("sa_lrs_limit_age",
      PARENT("sa_lrs", 1),
      INT_TAG);

  DECL("sa_passive_size",
      DOC("number fo clauses in the passive container"),
      PARENT("sa",3),
      INT_TAG);
  DECL("sa_active_size",
      DOC("number fo clauses in the active container"),
      PARENT("sa",3),
      INT_TAG);


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
      PARENT("ig_containers", 0),
      UNIT_TAG);
  DECL("ig_passive_added",
      PARENT("passive_clauses", 0),
      PARENT("ig_containers", 0),
      UNIT_TAG);
  DECL("ig_unprocessed_added",
      PARENT("unprocessed_clauses", 0),
      PARENT("ig_containers", 0),
      UNIT_TAG);


  DECL("ig_new_clause",
      PARENT("new_clauses", 0),
      PARENT("ig", 1),
      UNIT_TAG);

  DECL("ig_gen",
      DOC("generation of new clauses"),
      PARENT("ig", 1));

  DECL("ig_sat",
      DOC("traces calls to the SAT solver from inst-gen"),
      PARENT("ig", 1));
  DECL("ig_final_sat_model",
      DOC("satisfiable model given by sat solver that lead to the algorithm termination"),
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

  DECL("inf_hsp",
      DOC("hyper-superposition"),
      PARENT("inf",1));
  DECL("inf_hsp_attempts",
      DOC("hyper-superposition attempts to rewrite subterms"),
      PARENT("inf_hsp",4));
  DECL("inf_hsp_rwrs",
      DOC("hyper-superposition rewriters"),
      PARENT("inf_hsp",3));
  DECL("inf_hsp_cannot",
      DOC("hyper-superposition was performed but the result wasn't unifiable terms (we did too much rewriting)"),
      PARENT("inf_hsp",1));
  DECL("inf_hsp_gen",
      DOC("hyper-superposition generated units"),
      PARENT("inf_hsp",1),
      UNIT_TAG);
  DECL("inf_hsp_prems",
      DOC("hyper-superposition premises"),
      PARENT("inf_hsp",2));
  DECL("inf_hsp_res",
      DOC("hyper-superposition results after the intended simplification"),
      PARENT("inf_hsp",1),
      UNIT_TAG);

  //
  // Decison procedures
  //

  DECL("dp",
      DOC("decision procedures"));


  DECL("dp_cc",
      DOC("congruence closure"),
      PARENT("dp",1));
  DECL("dp_cc_interf",
      DOC("interface"),
      PARENT("dp_cc",1));
  DECL("dp_cc_interf_inp",
      DOC("added first-order literals"),
      PARENT("dp_cc_interf",1));
  DECL("dp_cc_interf_res",
      DOC("result statuses"),
      PARENT("dp_cc_interf",1));
  DECL("dp_cc_interf_unsat",
      DOC("unsatisfiable subset"),
      PARENT("dp_cc_interf",1));

  DECL("dp_cc_distinct",
      DOC("distinct constraints"),
      PARENT("dp_cc",3));

  DECL("dp_cc_fo_conv",
      DOC("conversion of first-order literals to internal represenation"),
      PARENT("dp_cc",1));

  DECL("dp_cc_const_intr",
      DOC("constant introductions"),
      PARENT("dp_cc",1));
  DECL("dp_cc_eqs_pending",
      DOC("pending equalities"),
      PARENT("dp_cc",1));
  DECL("dp_cc_unions",
      DOC("union operations"),
      PARENT("dp_cc",1));
  DECL("dp_cc_contr",
      DOC("contradiction pair"),
      PARENT("dp_cc",1));
  DECL("dp_cc_expl",
      DOC("explanation generation"),
      PARENT("dp_cc",1));
  DECL("dp_cc_expl_curr",
      DOC("currently explained pair"),
      PARENT("dp_cc_expl",1));
  DECL("dp_cc_expl_prem",
      DOC("premises of currently explained pair"),
      PARENT("dp_cc_expl",1));
  DECL("dp_cc_expl_planned",
      DOC("pairs that need to be explained"),
      PARENT("dp_cc_expl",1));
  DECL("dp_cc_expl_up",
      DOC("collection of unifying path"),
      PARENT("dp_cc_expl",2));

  //
  // SMT 
  //
  
  DECL("smt", 
      DOC("traces for SimpleSMT"));
  DECL("smt_sat_status",
      DOC("status of the SAT solver at each step"),
      PARENT("smt", 1));
  DECL("smt_dp_status", 
      DOC("status of the Decision Procedure "),
      PARENT("smt",1 ));
  DECL("smt_clause", 
      DOC("Traces the clauses added to the SAT solver"),
      PARENT("smt",1));
  DECL("smt_sat_clauses",
      DOC("initial sat clauses"),
      PARENT("smt",1));
  DECL("smt_confl_detail",
      DOC("details of smt conflicts"),
      PARENT("smt",1));


  //
  // Splitting with backtracking
  //

  DECL("bspl",
      DOC("traces for splitting with backtracking"));

  DECL("bspl_refutations",
      DOC("numbers of branch refutations leading to backtracking"),
      PARENT("bspl",1),
      UNIT_TAG);
  DECL("bspl_rm_backtracked",
      DOC("clause removals due to backtracking upon branch refutation"),
      PARENT("bspl",2),
      UNIT_TAG);
  DECL("bspl_rm_restored",
      DOC("restored claused due to backtracking upon branch refutation"),
      PARENT("bspl",2),
      UNIT_TAG);

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
      PARENT("sspl",3),
      UNIT_TAG);
  DECL("sspl_confl",
      DOC("SAT conflict clauses generated"),
      PARENT("sspl",0));
  DECL("sspl_confl_derivations",
      DOC("output derivations of SAT conflict clauses"),
      PARENT("sspl_confl",1));
  DECL("sspl_comp_names",
      DOC("introduced component names"),
      PARENT("sspl",1),
      UNIT_TAG);
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
      PARENT("sspl_rm",1),
      UNIT_TAG);
  DECL("sspl_rm_restored",
      DOC("restored claused due to backtracking upon change of component selection"),
      PARENT("sspl_rm",1),
      UNIT_TAG);

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
      PARENT("sspl_ns",0),
      UNIT_TAG);

  //
  // Preprocessing
  //

  DECL("pp",
      DOC("preprocessing traces"));

  DECL("pp_input",
      DOC("print-out the problem as received from the parser"),
      PARENT("pp",1));

  DECL("pp_pre_ennf",
      DOC("print-out the problem just before conversion to ennf"),
      PARENT("pp",1),
      UNIT_TAG);

  DECL("pp_pre_cl",
      DOC("print-out the problem just before clausification"),
      PARENT("pp",1),
      UNIT_TAG);
  DECL("pp_final",
      DOC("print-out the final cnf of the problem after preprocessing"),
      PARENT("pp",1));


  DECL("pp_sk",
      DOC("solemization"),
      PARENT("pp",1));
  DECL("pp_sk_funs",
      DOC("introduced skolem functions"),
      PARENT("pp_sk",0));
  DECL("pp_sk_nonconst_intr",
      DOC("trace introductions of non-constant skolem functions"),
      PARENT("pp_sk",0));

  DECL("pp_naming",
      DOC("naming"),
      PARENT("pp",1));
  DECL("pp_naming_args",
      DOC("units passed to naming"),
      PARENT("pp_naming",1),
      UNIT_TAG);
  DECL("pp_naming_defs",
      DOC("definitions introduced by naming"),
      PARENT("pp_naming",0),
      UNIT_TAG);

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
  DECL("pp_esk_cs_args",
      DOC("units processed by constant skolemization"),
      PARENT("pp_esk",1),
      UNIT_TAG);

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
  DECL("pp_inl_dep_added",
      DOC("dependency entry added"),
      PARENT("pp_inl_dep",1));
  DECL("pp_inl_dep_expand",
      DOC("dependencies of an entry expanded"),
      PARENT("pp_inl_dep",1));

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
  DECL("pp_ea_eq_sorts",
      DOC("sorts used in equality axiomatizer"),
      PARENT("pp_ea",1));
  DECL("pp_ea_eq_lit_builder",
      DOC("builder of equality literals"),
      PARENT("pp_ea",1));

  DECL("pp_ed",
      DOC("equivalence discovery"),
      PARENT("pp",1));
  DECL("pp_ed_progress",
      DOC("progress of the equivalence discovery algorithm"),
      PARENT("pp_ed",0));
  DECL("pp_ed_eq",
      DOC("discovered equivalences"),
      PARENT("pp_ed",1),
      UNIT_TAG);
  DECL("pp_ed_eq_prems",
      DOC("premises of discovered equivalences"),
      PARENT("pp_ed_eq",1));
  DECL("pp_ed_imp",
      DOC("discovered implications"),
      PARENT("pp_ed",1),
      UNIT_TAG);
  DECL("pp_ed_imp_prems",
      DOC("premises of discovered implications"),
      PARENT("pp_ed_imp",1));

  DECL("pp_aig",
      DOC("aig sub-formula sharing"),
      PARENT("pp",1));
  DECL("pp_quant_simpl",
      DOC("quantifiers simplified by AIGs"),
      PARENT("pp_aig",1));
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
  DECL("pp_aig_rwr",
      DOC("aig sharing formula rewriter"),
      PARENT("pp_aig",1));
  DECL("pp_aig_subst",
      DOC("aig substitution applications"),
      PARENT("pp_aig",1));
  DECL("pp_aig_subst_quant",
      DOC("quantifier transformations by substitutions"),
      PARENT("pp_aig_subst",1));

  DECL("pp_aigtr",
      DOC("AIGTransformer"),
      PARENT("pp_aig",1),
      PARENT("pp",1));
  DECL("pp_aigtr_inp_map",
      DOC("input map"),
      PARENT("pp_aigtr",0));
  DECL("pp_aigtr_sat",
      DOC("map saturation process"),
      PARENT("pp_aigtr",1));
  DECL("pp_aigtr_sat_deps",
      DOC("dependencies between rewrite rules"),
      PARENT("pp_aigtr_sat",1));

  DECL("pp_aig_compr",
      DOC("AIGCompressor"),
      PARENT("pp_aig",1));
  DECL("pp_aig_compr_succ",
      DOC("successfully compressed AIGs"),
      PARENT("pp_aig_compr",0));
  DECL("pp_aig_compr_loc_succ",
      DOC("local successfully compressed AIGs"),
      PARENT("pp_aig_compr",1));
  DECL("pp_aig_compr_all",
      DOC("all AIG compression attempts"),
      PARENT("pp_aig_compr",1));
  DECL("pp_aig_compr_lookup",
      DOC("BDD look-up"),
      PARENT("pp_aig_compr",1));
  DECL("pp_aig_compr_lookup_hit",
      DOC("hit of BDD look-up table"),
      PARENT("pp_aig_compr_lookup",1));
  DECL("pp_aig_compr_lookup_improvement",
      DOC("improvement for BDD look-up"),
      PARENT("pp_aig_compr_lookup",1));
  DECL("pp_aig_compr_lookup_map_improvement",
      DOC("improvement for BDD look-up in map"),
      PARENT("pp_aig_compr_lookup",1));
  DECL("pp_aig_compr_growth",
      DOC("local AIG compression attempts where the AIG has grown"),
      PARENT("pp_aig_compr",1));
  DECL("pp_aig_compr_bdd",
      DOC("display bdds used in local compressions"),
      PARENT("pp_aig_compr",2));
  DECL("pp_aig_compr_attempts",
      DOC("attempts for aig compression"),
      PARENT("pp_aig_compr",2));
  DECL("pp_aig_compr_forms",
      DOC("formulas modified by aig compression"),
      PARENT("pp_aig_compr",1));
  DECL("pp_aig_compr_units",
      DOC("units modified by aig compression"),
      PARENT("pp_aig_compr",2));
  DECL("pp_aig_compr_atom",
      DOC("units modified by aig compression"),
      PARENT("pp_aig_compr",3));

  DECL("pp_aiginl",
      DOC("AIG based inlining"),
      PARENT("pp_aig",1),
      PARENT("pp",1));
  DECL("pp_aiginl_equiv",
      DOC("added equivalences"),
      PARENT("pp_aiginl",1));
  DECL("pp_aiginl_instance",
      DOC("instantiated AIG of rhs of a definition"),
      PARENT("pp_aiginl",1));
  DECL("pp_aiginl_aig",
      DOC("result of inlining application on an AIG"),
      PARENT("pp_aiginl",1));
  DECL("pp_aiginl_unit",
      DOC("result of inlining on units"),
      PARENT("pp_aiginl",1));
  DECL("pp_aiginl_unit_args",
      DOC("units as they are passed to the apply() function"),
      PARENT("pp_aiginl",1),
      UNIT_TAG);


  DECL("pp_aigdef",
      DOC("AIG based definition introduction"),
      PARENT("pp_aig",1),
      PARENT("pp",1));
  DECL("pp_aigdef_intro",
      DOC("introduced definitions for AIG nodes"),
      PARENT("pp_aigdef",0),
      UNIT_TAG);
  DECL("pp_aigdef_apply",
      DOC("introducing definitions into formulas"),
      PARENT("pp_aigdef",1));
  DECL("pp_aigdef_apply_subform",
      DOC("introducing definitions into subformulas"),
      PARENT("pp_aigdef_apply",1));
  DECL("pp_aigdef_used_aigs",
      DOC("used AIGs"),
      PARENT("pp_aigdef",1));

  DECL("pp_pii",
      DOC("predicate index introduction"),
      PARENT("pp", 1));
  DECL("pp_pii_elim",
      DOC("eliminated predicates"),
      PARENT("pp_pii", 0));
  DECL("pp_pii_intro",
      DOC("introduced index predicates"),
      PARENT("pp_pii", 1));
  DECL("pp_pii_rwr",
      DOC("rewrites of eliminated predicates into indexed"),
      PARENT("pp_pii", 2));

  DECL("pp_ep",
      DOC("equality propagation"),
      PARENT("pp",1));
  DECL("pp_ep_args",
      DOC("units on which equality propagation is applied"),
      PARENT("pp_ep",1),
      UNIT_TAG);

  DECL("pp_tlf",
      DOC("top-level flattening"),
      PARENT("pp",1));
  DECL("pp_tlf_processed",
      DOC("units on which top-level flattening is applied"),
      PARENT("pp_tlf",1),
      UNIT_TAG);
  DECL("pp_tlf_res",
      DOC("results of top-level flattening"),
      PARENT("pp_tlf",1),
      UNIT_TAG);

  //
  // BFNT
  //

  DECL("bfnt");

  DECL("bfnt_cl",
      DOC("clauses generated by bfnt"),
      PARENT("bfnt",1),
      UNIT_TAG);
  DECL("bfnt_cl_ineq",
      DOC("bfnt clauses expressing inequalities between constants"),
      PARENT("bfnt_cl",0),
      UNIT_TAG);
  DECL("bfnt_cl_tot",
      DOC("bfnt clauses expressing totality of functions"),
      PARENT("bfnt_cl",0),
      UNIT_TAG);
  DECL("bfnt_cl_transf",
      DOC("problem clauses transformed to bfnt"),
      PARENT("bfnt_cl",0),
      UNIT_TAG);

  DECL("bfnt_loop",
      DOC("bfnt solving loop"),
      PARENT("bfnt",1));

  //
  // Interpolation
  //

  DECL("itp",
      DOC("interpolation traces"));

  DECL("itp_sub",
      DOC("generated sub-interpolants"),
      PARENT("itp",1));

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

  DECL("sat_min",
      DOC("sat model minimizer"),
      PARENT("sat",1));
  DECL("sat_min_sz",
      DOC("minimized model size"),
      PARENT("sat_min",0));
  DECL("sat_min_au",
      DOC("assignment update"),
      PARENT("sat_min",1));
  DECL("sat_min_sel",
      DOC("selected literals"),
      PARENT("sat_min",1));
  DECL("sat_min_mdl_chng",
      DOC("reflecting model changes"),
      PARENT("sat_min",2));
  DECL("sat_min_satisfied_clauses",
      DOC("satisfying and unsatisfying of clauses"),
      PARENT("sat_min",3));

  DECL("sat_iss",
      DOC("implicative simultaneous sat sweeping"),
      PARENT("sat",1));
  DECL("sat_iss_rand_sim",
      DOC("random simulation"),
      PARENT("sat_iss",1));
  DECL("sat_iss_grps",
      DOC("candidate groups"),
      PARENT("sat_iss",2));
  DECL("sat_iss_grps_content",
      DOC("content of candidate groups"),
      PARENT("sat_iss_grps",1));
  DECL("sat_iss_try_impl",
      DOC("attempts to prove implications"),
      PARENT("sat_iss",1));
  DECL("sat_iss_impl_scan",
      DOC("internal working of lookForImplications function"),
      PARENT("sat_iss",2));
  DECL("sat_iss_impl",
      DOC("discovered implications"),
      PARENT("sat_iss",2));
  DECL("sat_iss_equiv",
      DOC("discovered equivalences"),
      PARENT("sat_iss",1),
      PARENT("sat_iss_impl",0));
  DECL("sat_iss_equiv_class_sizes",
      DOC("sizes of final equivalence classes larger than 1"),
      PARENT("sat_iss",1),
      INT_TAG);


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
      DOC("traces related to Vampire API for problems"),
      PARENT("api",0));
  DECL("api_prb_transf",
      DOC("traces related to Vampire API problem transformations"),
      PARENT("api_prb",2));
  DECL("api_prb_prepr_progress",
      DOC("progress of the Problem::preprocess function"),
      PARENT("api_prb",1));

  //
  // VUtils
  //

  DECL("vu_z3ie",
      DOC("traces from z3 interpolant extractor"));

  DECL("vu_ers",
      DOC("traces from epr restoring scanner"));

  DECL("vu_sc",
      DOC("traces from SMTLIB concat"));
  DECL("vu_sc_files",
      DOC("input files"),
      PARENT("vu_sc",1));
  DECL("vu_sc_let",
      DOC("flet to let rewriting in SMTLIB --> SMTLIB2 conversion"),
      PARENT("vu_sc",1));

  //
  // Other
  //

  DECL("test_tag",
      DOC("trace tag to be used for testing"));

  DECL("lisp_rdr",
      DOC("List reading by LispListReader"));

  DECL("s2f",
      DOC("SAT2FO class for conversions between SAT and first-order"));
  DECL("s2f_confl",
      DOC("conflict clauses created by s2f"),
      PARENT("s2f",1),
      UNIT_TAG);


  DECL("bdd");
  DECL("bdd_clausifier",
      PARENT("bdd",1));
  DECL("bdd_triv_vars",
      DOC("trivial variables found in bdd"),
      PARENT("bdd",1));

  DECL("kbo");
  DECL("kbo_prec",
      PARENT("kbo",0));

  DECL("tab",
      DOC("tabulation"));

  DECL("ls_lookahead",
      DOC("look-ahead literal selection function (fn number 11)"),
      PARENT("ls",1));

  DECL("ft",
      DOC("formula transformer tracing"));
  DECL("ft_tl",
      DOC("top level transformation"),
      PARENT("ft",0));
  DECL("ft_subformula",
      DOC("subfomula transformation"),
      PARENT("ft",1));


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
      PARENT("arith",0),
      UNIT_TAG);

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

  DECL("ut",
      DOC("traces in the unit-testing infrastructure"));
  DECL("ut_forking",
      PARENT("ut",1));

  DECL("pt",
      DOC("proof transformation"));
  DECL("pt_units",
      DOC("transformations of units"),
      PARENT("pt",1));
  DECL("pt_simpl_aig",
      DOC("aigs involved in proof simplifier"),
      PARENT("pt",2));

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



  ENABLE_TAG("bug");
}


}

#endif
