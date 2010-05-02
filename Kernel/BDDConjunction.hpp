/**
 * @file BDDConjunction.hpp
 * Defines class BDDConjunction.
 */

#ifndef __BDDConjunction__
#define __BDDConjunction__

#include "../Kernel/BDDClausifier.hpp"

#include "../SAT/TWLSolver.hpp"

#include "../Forwards.hpp"

namespace Kernel {

using namespace SAT;

/**
 * A class of objects that keep a conjunction of multiple BDDs.
 *
 * Keeping conjunction of multiple BDDs using this class shows to
 * be more efficient for large BDDs than just using a BDD conjunction
 * operation, as here we use an incremental SAT solver to check whether
 * the conjunction is a satisfiable formula or not.
 */
class BDDConjunction
{
public:
  BDDConjunction();

  void addNode(BDDNode* n);

  /** Return @b true iff the conjunction represented by this object is unsatisfiable */
  bool isFalse() { return _isFalse; }
private:
  /** Is equal to @b true iff the conjunction represented by this object is unsatisfiable */
  bool _isFalse;

  BDDClausifier _clausifier;

  /**
   * Two-watched-literal incremental SAT solver that is used to check whether
   * the conjunction represented by this object is satisfiable
   */
  TWLSolver _solver;
};

}

#endif // __BDDConjunction__
