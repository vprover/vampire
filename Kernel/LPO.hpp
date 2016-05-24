/**
 * @file LPO.hpp
 * Defines class LPO for instances of the lexicographic path ordering
 *
 */

#ifndef __LPO__
#define __LPO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

#include "Ordering.hpp"

namespace Kernel {

class LPOBase
: public Ordering
{
public:  
  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2) const;

protected:
  LPOBase(Problem& prb, const Options& opt);

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
 * Class for instances of the lexicographic path orderings
 */
class LPO
: public LPOBase
{
public:
  CLASS_NAME(LPO);
  USE_ALLOCATOR(LPO);

  LPO(Problem& prb, const Options& opt) 
    : LPOBase(prb, opt)
  {}
  
  ~LPO() {}

  virtual Result compare(Literal* l1, Literal* l2) const;
  virtual Result compare(TermList tl1, TermList tl2) const;
protected:
};

}
#endif
