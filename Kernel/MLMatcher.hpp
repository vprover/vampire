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
  static bool canBeMatched(Clause* base, DArray<LiteralList*>& matches);

  static bool checkForSubsumptionResolution(Clause* base,
  	DArray<LiteralList*>& alts, Literal* resolvedInst);


private:
  template<class T>
  static void orderLiterals(T& base, unsigned baseLen, DArray<LiteralList*>& alts,
	  DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd);
};


};

#endif /* __MLMatcher__ */
