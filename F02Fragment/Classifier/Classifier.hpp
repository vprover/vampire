#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Clause.hpp"

namespace FO2Fragment {
using namespace Kernel;

/**
 * @brief Classifier for the FO2 (Two-Variable Fragment) logic.
 * Inspects parsed formulas/clauses to determine if the problem stays within the two-variable bound
 * and detects the presence of equality literals.
 */
class Classifier {

public:
  /**
   * @brief Analyzes the UnitList returned by the parser.
   * @param ul Pointer to the list of units (formulas or clauses).
   * @param hasEq Set to true if equality literals are found in the problem.
   * @return true if the problem belongs to the FO2 fragment, false otherwise.
   */
    static bool isFO2(UnitList *ul, bool &hasEq);

private:
  /**
   * @brief Recursive analysis of First-Order Formulas (FOF).
   * @param f Formula to analyze.
   * @param varSet Output: free variables of this subformula. Each subformula
   * must have at most two, allowing bound variables to be renamed and reused.
   * @param hasEq Flag set to true if an equality literal is encountered.
   * @return true if the formula belongs to the FO2 fragment, false otherwise.
   */
  static bool isFO2Formula(Formula *f, DHSet<unsigned> &varSet, bool &hasEq);

  /**
   * @brief Analysis of CNF clauses.
   * @param clause Clause to analyze.
   * @param vars Set of variables in the clause.
   * @param hasEq Flag set to true if an equality literal is encountered.
   * @return true if the clause belongs to the FO2 fragment, false otherwise.
   */
  static bool isFO2Clause(Clause *clause, DHSet<unsigned> &vars, bool &hasEq);
};
} // namespace FO2Fragment
