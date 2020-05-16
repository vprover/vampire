
/*
 * File ProxyElimination.hpp.
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
 * @file ProxyElimination.hpp
 * Defines class ProxyElimination.
 */

#ifndef __PROXY_ELIMINATION__
#define __PROXY_ELIMINATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"

#include "Lib/Stack.hpp"

#include <memory>

namespace Inferences {

class ProxyElimination
{
public:

  CLASS_NAME(ProxyElimination);
  USE_ALLOCATOR(ProxyElimination);

  struct ConstantTerm{
    
    CLASS_NAME(ConstantTerm);
    USE_ALLOCATOR(ConstantTerm);
    
    Signature::Proxy prox;
    Term* constant;
    Stack<TermList> args; //first arg at top
    Stack<TermList> sorts; //first sort at top
    int onRight;
    
    ConstantTerm() {}
  };

  typedef unique_ptr<ConstantTerm> ct_ptr;

  static ct_ptr isHolConstantApp(TermList tl, unsigned unaryBinaryOrTenary);
  static ct_ptr isHolConstantApp(Literal* lit, unsigned unaryBinaryOrTenary);
  static Inference::Rule constToInfRule(Signature::Proxy cnst);
  static TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt);
  static TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt);
  static int isBoolValue(TermList tl);
  static bool isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &applyPIrule, TermList &srt1);
  static bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, TermList &sort);
  static bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2);
  static bool isNOTEquality(Literal* lit, TermList &newEqlhs, TermList &newEqrhs, bool &polarity);
  static Clause* replaceLit2(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d = 0, Literal* e = 0);


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

  class NOTRemovalGIE
    : public GeneratingInferenceEngine
  {
  public:
    CLASS_NAME(NOTRemovalGIE);
    USE_ALLOCATOR(NOTRemovalGIE);
    
    ClauseIterator generateClauses(Kernel::Clause* c);
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

  class ProxyEliminationISE : public ImmediateSimplificationEngine {
    public:
      CLASS_NAME(ProxyEliminationISE);
      USE_ALLOCATOR(ProxyEliminationISE);
  	  ClauseIterator simplifyMany(Clause* c);
      Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }

    private:
      struct ProxyEliminationIterator;
      struct ProxyEliminationFn;

  };


}; //of ProxyElimination

}
#endif
