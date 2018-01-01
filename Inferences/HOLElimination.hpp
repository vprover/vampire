
/*
 * File HOLElimination.hpp.
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
 * @file HOLElimination.hpp
 * Defines class HOLElimination.
 */

#ifndef __HOL_ELIMINATION__
#define __HOL_ELIMINATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

/*
  Simplification rules:

  vAPP(vNOT, t1) = $true \/ C
  ----------------------------
       t1 = $false \/ C

  vAPP(vNOT t1) = $false \/ C
  ---------------------------
       t1 = $true \/ C

*/
class NOTRemovalISE
  : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(NOTRemovalISE);
  USE_ALLOCATOR(NOTRemovalISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

/*
  Simplification rules:

  vAPP(vAPP(vOR, t1), t2) = $true \/ C
  ------------------------------------
      t1 = $true \/ t2 = $true \/ C

  vAPP(vAPP(vIMP, t1), t2) = $true \/ C
  -------------------------------------
      t1 = $false \/ t2 = $true \/ C

  vAPP(vAPP(vAND, t1), t2) = $false \/ C
  -------------------------------------
      t1 = $false \/ t2 = $false \/ C  
		  
*/
class ORIMPANDRemovalISE
  : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(ORIMPRemovalISE);
  USE_ALLOCATOR(ORIMPRemovalISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

class HOLElimination : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(ANDElimination);
    USE_ALLOCATOR(ANDElimination);
    ClauseIterator generateClauses(Clause* premise);
};

}

#endif
