
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
#include "Kernel/HOSortHelper.hpp"
#include <memory>

namespace Inferences {

struct ConstantTerm{
  
  CLASS_NAME(ConstantTerm);
  USE_ALLOCATOR(ConstantTerm);
  
  Signature::Symbol::HOLConstant cnst;
  Term* constant;
  Stack<TermList> args; //first arg at top
  Stack<unsigned> sorts; //first sort at top
  int onRight;
  
  ConstantTerm() {}
};


typedef Signature::Symbol SS;
typedef unique_ptr<ConstantTerm> ct_ptr;
//ct_ptr isHolConstantApp(Literal* lit, unsigned unaryBinaryOrTenary, bool flex = false);
//ct_ptr isHolConstantApp(TermList tl, unsigned unaryBinaryOrTenary);


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

  vAPP(vAPP(vEQUALS, t1), t2) = $true \/ C
  ----------------------------------------
             t1 = t2 \/ C

  vAPP(vAPP(vEQUALS, t1), t2) = $false \/ C
  -----------------------------------------
            ~(t1 = t2) \/ C

*/

class EQUALSRemovalISE
   : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(EQUALSRemovalISE);
  USE_ALLOCATOR(EQUALSRemovalISE);
  
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
  CLASS_NAME(ORIMPANDRemovalISE);
  USE_ALLOCATOR(ORIMPANDRemovalISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class ORIMPANDRemovalISE2
  : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(ORIMPANDRemovalISE2);
  USE_ALLOCATOR(ORIMPANDRemovalISE2);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

/*
  Simplification rules:

  vAPP(vPI, t1) = $true \/ C
  --------------------------
   vAPP(t1, X) = $true \/ C

   
      vAPP(vPI, t1) = $false \/ C
  ----------------------------------
   vAPP(t1, f(X1..Xn)) = $true \/ C

The converse of the above rules for vSIGMA   
		  
*/

class PISIGMARemovalISE
   : public ImmediateSimplificationEngine
{
	
public:
  CLASS_NAME(PISIGMARemovalISE);
  USE_ALLOCATOR(PISIGMARemovalISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);	   
};

/*Generating rules:
  
  vAPP(vAPP(vOR, t1), t2) = $false \/ C
  ------------------------------------
           t1 = $false \/ C
	       t2 = $false \/ C

  vAPP(vAPP(vIMP, t1), t2) = $false \/ C
  -------------------------------------
           t1 = $true \/ C 
	       t2 = $false \/ C

  vAPP(vAPP(vAND, t1), t2) = $true \/ C
  -------------------------------------
           t1 = $true \/ C 
	       t2 = $true \/ C 
  
  vAPP(vAPP(vIFF, t1), t2) = $true \/ C
  -------------------------------------
     t1 = $true \/ t2 = $false \/ C 
	 t1 = $false \/ t2 = $true \/ C   

  vAPP(vAPP(vIFF, t1), t2) = $false \/ C
  -------------------------------------
      t1 = $true \/ t2 = $true \/ C 
	 t1 = $false \/ t2 = $false \/ C 

  vAPP(vAPP(vXOR, t1), t2) = $true \/ C
  -------------------------------------
     t1 = $true \/ t2 = $true \/ C 
	t1 = $false \/ t2 = $false \/ C 

  vAPP(vAPP(vXOR, t1), t2) = $false \/ C
  -------------------------------------
     t1 = $true \/ t2 = $false \/ C 
	 t1 = $false \/ t2 = $true \/ C	
*/

class ORIMPANDIFFXORRemovalGIE : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(ORIMPANDIFFXORRemovalGIE);
    USE_ALLOCATOR(ORIMPANDIFFXORRemovalGIE);
	Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

  private:
    struct ProxyEliminationIterator;
    struct ProxyEliminationFn;

};

/* implements the following inference rules:

  C[app(I, t1)]
  -------------
      C[t1]

  C[app(app(K, t1), t2)]		  
  ----------------------
         C[t1]

  C[app(app(app(B, t1), t2), t3)]
  -------------------------------
       C[app(t1,app(t2,t3))]

  C[app(app(app(C, t1), t2), t3)]
  -------------------------------
       C[app(app(t1,t3),t2)]
	   
  C[app(app(app(S, t1), t2), t3)]
  -------------------------------
   C[app(app(t1,t3),app(t2, t3)]
	   
*/

class CombinatorEliminationISE : public ImmediateSimplificationEngine {

public:
  CLASS_NAME(CombinatorEliminationISE);
  USE_ALLOCATOR(CombinatorEliminationISE);
  
  Kernel::Clause* simplify(Kernel::Clause* premise);		
	
};

}

#endif
