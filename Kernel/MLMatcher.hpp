/**
 * @file MLMatcher.hpp
 * Defines class MLMatcher with methods
 * supporting multiliteral matching.
 */


#ifndef __MLMatcher__
#define __MLMatcher__

#include "../Forwards.hpp"

namespace Kernel {

using namespace Lib;

class MLMatcher {
public:
  static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts,
  	Literal* resolvedLit, bool multiset);
  static bool canBeMatched(Clause* base, Clause* instance, LiteralList** alts,
  	Literal* resolvedLit)
  {
    return canBeMatched(base->literals(), base->length(), instance, alts, resolvedLit, resolvedLit==0);
  }


  static bool canBeMatched(Clause* base, DArray<LiteralList*>& matches);


private:
  template<class T, class U>
  static void orderLiterals(T& base, U& alts,
	  DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd);
};


};

#endif /* __MLMatcher__ */
