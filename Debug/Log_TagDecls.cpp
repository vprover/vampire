/**
 * @file Log_TagDecls.cpp
 * Implements class Log_TagDecls.
 */

#include "Log.hpp"
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
      PARENT("sa_new_clause", 0),
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

  DECL("inf_ie",
      DOC("interpreted evaluation"),
      PARENT("inf",1),
      PARENT("arith",1));


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

  DECL("pp_hr",
      DOC("horn revealer"),
      PARENT("pp",1));

  DECL("pp_inl",
      DOC("predicate definition inlining"),
      PARENT("pp",1));
  DECL("pp_inl_def",
      DOC("definition added"),
      PARENT("pp_inl",0));
  DECL("pp_inl_step",
      DOC("inlining step"),
      PARENT("pp_inl",0));
  DECL("pp_inl_substep",
      DOC("inlining substeps"),
      PARENT("pp_inl_step",1));
  DECL("pp_inl_dep",
      DOC("tracing dependencies between predicates"),
      PARENT("pp_inl",1));

  DECL("pp_tpr",
      DOC("trivial predicate remover"),
      PARENT("pp",1));


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

  //
  // Multiprocessing
  //

  DECL("mp",
      DOC("tracing of multiprocessing features"));

  DECL("mp_sem",
      DOC("tracing of semaphores"),
      PARENT("mp",1));


  //
  // Other
  //

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

  DECL("prb_prop_refresh",
      DOC("logs when property of a problem needs to be updated by traversing through the problem"));

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
}


}
