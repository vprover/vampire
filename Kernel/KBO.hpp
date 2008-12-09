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
  Result compare(const Literal* l1,const Literal* l2);
  Result compare(const TermList* t1,const TermList* t2);
private:
  class State;
  /** Weight of variables */
  int _variableWeight;
  /** Weight of predicate and function symbols not occurring in the
   * signature */
  int _defaultSymbolWeight;

  int functionSymbolWeight(unsigned fun) { return _defaultSymbolWeight; }
  int predicateHeaderWeight(unsigned pred) { return _defaultSymbolWeight; }

  int functionPrecedence(unsigned fun) { return fun; }
  int predicatePrecedence(unsigned pred);
  int predicateLevel(unsigned pred);

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
