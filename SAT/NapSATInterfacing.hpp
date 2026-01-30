/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MinisatInterfacing.hpp
 * Defines class MinisatInterfacing
 */
#ifndef __NapSATInterfacing__
#define __NapSATInterfacing__

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "NapSAT/include/SAT-types.hpp"
#include "NapSAT/include/SAT-API.hpp"
#include <functional>

namespace SAT {

class NapSATInterfacing : public SATSolver
{
public:
  NapSATInterfacing(std::function<double(SATLiteral)> func = nullptr);
  ~NapSATInterfacing() override;

  void addClause(SATClause* cl) override;

  VarAssignment getAssignment(unsigned var) override;

  bool isZeroImplied(unsigned var) override;

  void ensureVarCount(unsigned newVarCnt) override;

  unsigned newVar() override;

  void suggestPolarity(unsigned var, unsigned pol) override;

  Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps,
                                      unsigned conflictCountLimit) override;

  SATLiteralStack failedAssumptions() override;

  static SATClauseList* minimizePremiseList(SATClauseList* premises,
                                            SATLiteralStack& assumps);

  SATClauseList *minimizePremises(SATClauseList *premises) override;

protected:
  napsat::Tvar vampireVar2NapSAT(unsigned vvar) const {
    return vvar;
  }

  unsigned napSATVar2Vampire(napsat::Tvar nvar) const {
    return (unsigned)(nvar);
  }

  const napsat::Tlit vampireLit2NapSAT(SATLiteral vlit) const {
    return napsat::literal(vampireVar2NapSAT(vlit.var()), vlit.positive());
  }


  const SATLiteral napSATLit2Vampire(napsat::Tlit nlit) const {
    return SATLiteral(napSATVar2Vampire(napsat::lit_to_var(nlit)), napsat::lit_pol(nlit) ? 1 : 0);
  }

  double weightFunction(napsat::Tlit lit) const {
    if (_vampire_weightFunction) {
      return _vampire_weightFunction(napSATLit2Vampire(lit));
    }
    return 1.0;
  }

private:
  napsat::status _status = napsat::status::SAT;
  std::vector<napsat::Tlit> _assumptions;
  napsat::NapSAT* _solver;

  /**
   * @brief Maps the napsat::Tclause added by the solver to the SATClause* added by Vampire.
   */
  std::vector<SATClause*> _addedClauses;

  std::function<double(SATLiteral)> _vampire_weightFunction;
};

}//end SAT namespace

 #endif /* __NapSATInterfacing__ */
