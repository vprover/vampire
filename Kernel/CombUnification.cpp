
/*
 * File CombUnification.cpp.
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
 * @file CombUnification.cpp
 * Implements polynomial modification of the Robinson unification algorithm.
 */

#include "Lib/Environment.hpp"

#include "Lib/Hash.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Random.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/Int.hpp"

#include "Clause.hpp"
#include "Renaming.hpp"
#include "SortHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Signature.hpp"

#include "Indexing/TermSharing.hpp"

#include "CombUnification.hpp"

#if VDEBUG
#include "Lib/Int.hpp"
#include "Debug/Tracer.hpp"
#include <iostream>
using namespace Debug;
#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

void CombSubstitution::populateTransformations()
{
  CALL("CombSubstitution::populateTransformations");

  UnificationPair up = _unificationPairs.top();
  TTPair topPair = up.unifPair;
  TermSpec tsLeft = topPair.first;
  TermSpec tsRght = topPair.second; 

  unsigned arityl, arityr;
  TermList headl = head(tsLeft, arityl);
  TermList headr = head(tsRght, arityr);
  
  int as = isComb(headl, arityl);

  if(as > 1){
  	Transform trs((AlgorithmStep)as,SECOND);
  	up.transformsLeft.push(trs);
  } 

}
  
/**
  * Returns the head symbol of an applicative term. 
  * @author Ahmed Bhayat
  * @location Manchester
  */
 
TermList CombSubstitution::head(TermSpec tspec, unsigned& arity)
{
  CALL("CombSubstitution::head");
  
  TermList ts = tspec.term;
  arity = 0;

  if(ts.isVar()){
    return ts;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    while(sym->hOLAPP()){
      arity++;
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return ts;
      }
      sym = env.signature->getFunction(ts.term()->functor());
    }
    return ts;
  }
}


/**
  * Returns 0 if not a combinator, 1 if is combinator not fully applied
  * and the relavant AlgorithmStep otherwise 
  * @author Ahmed Bhayat
  * @location Manchester
  */
int CombSubstitution::isComb(TermList tl, unsigned arity) const
{

  CALL("CombSubstitution::isComb");

  if(tl.isVar()){ return 0; }
  SS* sym = env.signature->getFunction(tl.term()->functor());
  switch(sym->getConst()){
    case SS::I_COMB:
      return arity >= 1 ? I_REDUCE : 1;
    case SS::K_COMB:
      return arity >= 2 ? K_REDUCE : 1;
    case SS::B_COMB:
      return arity >= 3 ? B_REDUCE : 1;
    case SS::C_COMB:
      return arity >= 3 ? C_REDUCE : 1;
    case SS::S_COMB:
      return arity >= 3 ? S_REDUCE : 1;
    default:
      return 0;      
  }
}

}