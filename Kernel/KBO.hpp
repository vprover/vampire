/**
 * @file KBO.hpp
 * Defines class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __KBO__
#define __KBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;

class KBOBase
: public Ordering
{
public:
  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2) const;

protected:
  KBOBase(Problem& prb, const Options& opt);

  Result compareFunctionPrecedences(unsigned fun1, unsigned fun2) const;

  int predicatePrecedence(unsigned pred) const;
  int predicateLevel(unsigned pred) const;

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
};

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
: public KBOBase
{
public:
  KBO(Problem& prb, const Options& opt);
  virtual ~KBO();

  virtual Result compare(Literal* l1, Literal* l2) const;
  virtual Result compare(TermList tl1, TermList tl2) const;
protected:

  class State;
  /** Weight of variables */
  int _variableWeight;
  /** Weight of function symbols not occurring in the
   * signature */
  int _defaultSymbolWeight;

  int functionSymbolWeight(unsigned fun) const;

  bool allConstantsHeavierThanVariables() const { return false; }
  bool existsZeroWeightUnaryFunction() const { return false; }


  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
};

}
#endif
