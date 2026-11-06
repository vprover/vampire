#ifndef __FO2Inferences__
#define __FO2Inferences__

#include "FO2Resolution.hpp"
#include <vector>

namespace FO2Fragment {

class FO2Inferences {
public:
  /**
   * Partition a clause into two nonempty parts with disjoint variable sets.
   * Output vectors must initially be empty. On failure they remain empty.
   * Preserves literal order within each part; ground-only clauses are not split.
   * The caller must explore the parts as alternative problems, not add both
   * as unconditional conclusions to the same saturation queue.
   */
  static bool partitionClause(Kernel::Clause* clause,
                              std::vector<Kernel::Literal*>& r1,
                              std::vector<Kernel::Literal*>& r2);

  /**
   * @brief Performs resolution between selected literals of icl1 and icl2.
   * Resolves selected literal at position litIdx1 in icl1 with selected literal at position litIdx2 in icl2.
   * Resolvent literals inherit indices from parent literals.
   * Returns true if resolution produced a resolvent, false otherwise.
   */
  static bool resolve(const IndexedClause& icl1, size_t litIdx1,
                      const IndexedClause& icl2, size_t litIdx2,
                      IndexedClause& outResolvent);

  /**
   * @brief Performs factoring on an indexed clause.
   * Factors selected literal at position litIdx1 with literal at position litIdx2.
   * Returns true if factoring produced a factor, false otherwise.
   */
  static bool factor(const IndexedClause& icl, size_t litIdx1, size_t litIdx2,
                     IndexedClause& outFactor);

  /**
   * @brief Checks indexed subsumption.
   * Returns true if icl1 subsumes icl2 (matching literals AND indices).
   */
  static bool subsumes(const IndexedClause& icl1, const IndexedClause& icl2);

  // Shorten by a selected unit resolution only when the unit matches the
  // target without instantiating its variables, and the result stays in S2+i.
  static bool simplifyWithUnit(const IndexedClause& clause, const IndexedClause& unit,
                               IndexedClause& result);

  /**
   * @brief Normalizes variable indices in an indexed clause (renaming them to 0, 1, 2... in order of appearance)
   * and removes duplicate literals under the normalized variable names.
   */
  static bool normalizeVariables(const IndexedClause& inIcl, IndexedClause& outIcl);

  /**
   * @brief Checks that an indexed clause satisfies the S2 conditions (Definition 6):
   *  (1) at most 2 variables and no nested function symbols,
   *  (2) a clause containing a ground (non-propositional) literal is entirely ground,
   *  (3) every functional term that is not ground contains all variables of the clause,
   *  (4) a 2-variable clause has a literal containing both variables.
   * Used to empirically verify the invariance property (Lemma 10, de Nivelle) of the
   * inference rules. Returns true if the clause is in S2; otherwise fills outReason.
   */
  static bool checkS2Invariant(const IndexedClause& icl, std::string& outReason);

  /**
   * @brief Index condition used in the proof of Lemma 10: in a clause with two variables a
   * literal has index 1 iff it is a two-variable literal; in a clause with at most one variable
   * every literal has index 0.
   */
  static bool checkIndexInvariant(const IndexedClause& icl, std::string& outReason);

  /**
   * @brief Hypothesis of Lemma 10 (Lemma 9): every selected literal B of a clause c satisfies
   * Vars(B) = Vars(c). Returns false and fills outReason if a selected literal does not.
   */
  static bool checkSelectionCoversVars(const IndexedClause& icl, std::string& outReason);
};

} // namespace FO2Fragment

#endif // __FO2Inferences__
