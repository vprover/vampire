#include "SAT/NapSATInterfacing.hpp"
#include "NapSATInterfacing.hpp"

#include <iostream>

using namespace napsat;
using namespace std;


namespace SAT
{
  NapSATInterfacing::NapSATInterfacing()
  {
    std::vector<std::string> env_args;
    env_args.push_back("--invariant-configuration-folder");
    env_args.push_back("../NapSAT/invariant-configurations/");
    env_args.push_back("-sw"); // suppress warnings
    env::extract_environment_variables(env_args);

    std::vector<std::string> opt_args;
    opt_args.push_back("-gb");
    // opt_args.push_back("-c"); // enable checking invariants
    // opt_args.push_back("-o"); // enable observer
    opt_args.push_back("--restarts");
    opt_args.push_back("off");
    opt_args.push_back("-del");
    opt_args.push_back("off");
    opt_args.push_back("--backtrack-possibilities-limit");
    opt_args.push_back("5000");
    napsat::options opts(opt_args);

    _solver = create_solver(0, 0, opts);
  }

  NapSATInterfacing::~NapSATInterfacing() {
    delete_solver(_solver);
  }

  unsigned NapSATInterfacing::newVar() {
    return new_variable(_solver);
  }


  inline void NapSATInterfacing::addClause(SATClause* cl)
  {
    start_new_clause(_solver);
    for (unsigned i = 0; i < cl->length(); i++) {
      push_literal(_solver, vampireLit2NapSAT((*cl)[i]));
    }
    Tclause napsat_cl = finalize_clause(_solver);

    if (napsat_cl == CLAUSE_UNDEF) { // the solver deleted the clause upon addition
      return;
    }
    if (napsat_cl >= _addedClauses.size()) {
      _addedClauses.resize(napsat_cl + 1, nullptr);
    }
    _addedClauses[napsat_cl] = cl;
  }


  VarAssignment NapSATInterfacing::getAssignment(unsigned var)
  {
    napsat::Tval val = get_variable_value(_solver, vampireVar2NapSAT(var));
    switch (val) {
    case napsat::VAR_TRUE:
      return VarAssignment::TRUE;
    case napsat::VAR_FALSE:
      return VarAssignment::FALSE;
    case napsat::VAR_UNDEF:
      return VarAssignment::NOT_KNOWN;
    default:
      ASSERTION_VIOLATION;
    }
  }


  bool NapSATInterfacing::isZeroImplied(unsigned var)
  {
    return is_root_level(_solver, vampireVar2NapSAT(var));
  }


  void NapSATInterfacing::ensureVarCount(unsigned newVarCnt)
  {
    while (newVarCnt > variables_count(_solver)) {
      new_variable(_solver);
    }
  }


  void NapSATInterfacing::suggestPolarity(unsigned var, unsigned pol)
  {
    suggest_polarity(_solver, vampireVar2NapSAT(var), pol);
  }


  Status NapSATInterfacing::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
  {
    std::vector<napsat::Tlit> napsat_assumptions;
    for (unsigned i = 0; i < assumps.size(); i++) {
      napsat_assumptions.push_back(vampireLit2NapSAT(assumps[i]));
    }
    add_assumption(_solver, napsat_assumptions);
    _status = solve_limited(_solver, conflictCountLimit);
    switch (_status) {
    case napsat::status::SAT:
      return Status::SATISFIABLE;
    case napsat::status::UNSAT:
      return Status::UNSATISFIABLE;
    case napsat::status::UNKNOWN:
      return Status::UNKNOWN;
    default:
      ASSERTION_VIOLATION;
    }
  }


  SATLiteralStack NapSATInterfacing::failedAssumptions()
  {
    SATLiteralStack result;
    std::vector<napsat::Tlit> failed = napsat::unsat_core(_solver);
    for (unsigned i = 0; i < failed.size(); i++) {
      result.push(napSATLit2Vampire(failed[i]));
    }
    return result;
  }


  SATClauseList* NapSATInterfacing::minimizePremiseList(SATClauseList* premises, SATLiteralStack& assumps)
  {
    return nullptr;
  }

  SATClauseList* NapSATInterfacing::minimizePremises(SATClauseList* premises)
  {
    return nullptr;
  }
} // namespace SAT
