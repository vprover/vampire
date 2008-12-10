/**
 * @file KBO.hpp
 * Defines class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __KBO__

#include "../Forwards.hpp"
#include "Ordering.hpp"

namespace Kernel {


/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
  : public Ordering
{
public:
  KBO(const Signature&);
  ~KBO();
  Result compare(Literal* l1, Literal* l2);
  Result compare(TermList* t1, TermList* t2);
  static KBO* createReversedAgePreferenceConstantLevels();
private:
  class State;
  /** Weight of variables */
  int _variableWeight;
  /** Weight of predicate and function symbols not occurring in the
   * signature */
  int _defaultSymbolWeight;

  int functionSymbolWeight(unsigned fun) { return _defaultSymbolWeight; }
  int predicateHeaderWeight(unsigned pred) { return _defaultSymbolWeight; }

  int functionPrecedence(unsigned fun);
  int predicatePrecedence(unsigned pred);
  int predicateLevel(unsigned pred);

  bool allConstantsHeavierThanVariables() { return false; }
  bool existsZeroWeightUnaryFunction() { return false; }

  /** number of predicates in the signature at the time the order was created */
  unsigned _predicates;
  /** number of functions in the signature at the time the order was created */
  unsigned _functions;
  /** Array of predicate levels */
  int* _predicateLevels;
  /** Array of predicate precedences */
  int* _predicatePrecedences;
  /** Array of function precedences */
  int* _functionPrecedences;
}; // class KBO

}
#endif
