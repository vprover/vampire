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
  static bool canBeMatched(Clause* base, Clause* instance, LiteralList** alts,
  	Literal* resolvedLit);


  static bool canBeMatched(Clause* base, LiteralList** matches);
  static bool canBeMatched(Clause* base, DArray<LiteralList*>& matches);

  static bool checkForSubsumptionResolution(Clause* base,
  	LiteralList** alts, Literal* resolvedInst);


private:
  template<class T, class U>
  static void orderLiterals(T& base, U& alts,
	  DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd);
};


};

#endif /* __MLMatcher__ */
