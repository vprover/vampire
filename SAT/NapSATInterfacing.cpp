#include "SAT/NapSATInterfacing.hpp"
#include "NapSATInterfacing.hpp"

using namespace napsat;


namespace SAT
{
  NapSATInterfacing::NapSATInterfacing()
  {
    std::vector<std::string> opt_args;
    opt_args.push_back("-gb");
    opt_args.push_back("-o");
    napsat::options opts(opt_args);

    _solver = create_solver(0, 0, opts);
  }

  NapSATInterfacing::~NapSATInterfacing() {
    delete _solver;
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
    finalize_clause(_solver);
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
    _status = static_cast<napsat::status>(solve_limited(_solver, conflictCountLimit));
  }


  SATLiteralStack NapSATInterfacing::failedAssumptions()
  {
    SATLiteralStack result;
    std::vector<napsat::Tlit> failed = napsat::failed_assumptions(_solver);
    for (unsigned i = 0; i < failed.size(); i++) {
      result.push(napSATLit2Vampire(failed[i]));
    }
    return result;
  }


  SATClauseList* NapSATInterfacing::minimizePremiseList(SATClauseList* premises, SATLiteralStack& assumps)
  {
    return nullptr;
  }


  void NapSATInterfacing::interpolateViaAssumptions(unsigned maxVar,
                                                    const SATClauseStack& first,
                                                    const SATClauseStack& second,
                                                    SATClauseStack& result)
  {}


  SATClauseList* NapSATInterfacing::minimizePremises(SATClauseList* premises)
  {
    return nullptr;
  }
} // namespace SAT
