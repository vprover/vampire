/**
 * @file KBO.hpp
 * Defines class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __KBO__

#include "../Forwards.hpp"

#include "../Lib/DArray.hpp"

#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
  : public Ordering
{
public:
  Result compare(Literal* l1, Literal* l2);
  Result compare(TermList tl1, TermList tl2);

  Comparison compareFunctors(unsigned fun1, unsigned fun2);
  
  static KBO* create();
private:
  KBO(const Signature&);
  ~KBO();

  class EqCmp;
  class State;
  /** Weight of variables */
  int _variableWeight;
  /** Weight of function symbols not occurring in the
   * signature */
  int _defaultSymbolWeight;

  void createEqualityComparator();
  void destroyEqualityComparator();
  Result compareEqualities(Literal* eq1, Literal* eq2);

  Result compareFunctionPrecedences(unsigned fun1, unsigned fun2);

  int functionSymbolWeight(unsigned fun);
  int predicatePrecedence(unsigned pred);
  int predicateLevel(unsigned pred);

  bool allConstantsHeavierThanVariables() { return false; }
  bool existsZeroWeightUnaryFunction() { return false; }

  /** number of predicates in the signature at the time the order was created */
  unsigned _predicates;
  /** number of functions in the signature at the time the order was created */
  unsigned _functions;
  /** Array of predicate levels */
  DArray<int> _predicateLevels;
  /** Array of predicate precedences */
  DArray<int> _predicatePrecedences;
  /** Array of function precedences */
  DArray<int> _functionPrecedences;

  bool _reverseLCM;

  /**
   * State used for comparing terms and literals
   */
  State* _state;

  /** Object used to compare equalities */
  EqCmp* _eqCmp;
};

}
#endif
