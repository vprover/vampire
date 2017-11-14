
/*
 * File MLMatcher.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file MLMatcher.hpp
 * Defines class MLMatcher with methods
 * supporting multiliteral matching.
 */


#ifndef __MLMatcher__
#define __MLMatcher__

#include "Forwards.hpp"

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
