
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

#ifndef __CNFOnTheFly__
#define __CNFOnTheFly__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

#include <memory>

namespace Inferences {
using namespace Indexing;

static Clause* replaceLits(Clause *c, Literal *a, Literal *b, Inference *inf, Literal *d = 0, Literal* e = 0);
static TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt);
static TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt);
static Inference::Rule convert(Signature::Proxy cnst);
static ClauseIterator produceClauses(Clause* c, bool generating, SkolemisingFormulaIndex* index = 0);


class IFFXORRewriterISE
  : public ImmediateSimplificationEngine
{
public:

  CLASS_NAME(IFFXORRewriterISE);
  USE_ALLOCATOR(IFFXORRewriterISE);

  Clause* simplify(Clause* c);
};

class EagerClausificationISE
  : public ImmediateSimplificationEngine
{
public:

  CLASS_NAME(EagerClausificationISE);
  USE_ALLOCATOR(EagerClausificationISE);

  ClauseIterator simplifyMany(Clause* c);
  Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }

};

class LazyClausification
  : public SimplificationEngine
{
public:
  CLASS_NAME(LazyClausification);
  USE_ALLOCATOR(LazyClausification);

  LazyClausification(){
    _formulaIndex = 0;
  }

  ClauseIterator perform(Clause* c);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

class LazyClausificationGIE
  : public GeneratingInferenceEngine
{
public:

  CLASS_NAME(LazyClausificationGIE);
  USE_ALLOCATOR(LazyClausificationGIE);

  LazyClausificationGIE(){
    _formulaIndex = 0;
  }

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* c);

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

/*class NOTRemovalGIE
  : public GeneratingInferenceEngine
{
public:
  CLASS_NAME(NOTRemovalGIE);
  USE_ALLOCATOR(NOTRemovalGIE);
  
  ClauseIterator generateClauses(Kernel::Clause* c);
};*/
/*
class EQUALSRemovalISE
   : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(EQUALSRemovalISE);
  USE_ALLOCATOR(EQUALSRemovalISE);
  
  bool isEQUALSApp(Literal* lit, TermList &t1, TermList &t2, bool &positive, TermList &sort);
  Kernel::Clause* simplify(Kernel::Clause* c);        
};


class ORIMPANDRemovalISE
  : public ImmediateSimplificationEngine
{

public:
  CLASS_NAME(ORIMPANDRemovalISE);
  USE_ALLOCATOR(ORIMPANDRemovalISE);
  
  bool appOfORorIMPorAND(Literal* lit, TermList &lhs1, TermList &rhs1, TermList &lhs2, TermList &rhs2);  
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class PISIGMARemovalISE
   : public ImmediateSimplificationEngine
{
  
public:
  CLASS_NAME(PISIGMARemovalISE);
  USE_ALLOCATOR(PISIGMARemovalISE);
  
  bool isPISIGMAapp(Literal* lit, TermList &t1, TermList &rhs, bool &applyPIrule, TermList &srt1);  
  Kernel::Clause* simplify(Kernel::Clause* c);     
};


class ProxyEliminationISE 
  : public ImmediateSimplificationEngine {
  public:
    CLASS_NAME(ProxyEliminationISE);
    USE_ALLOCATOR(ProxyEliminationISE);
    ClauseIterator simplifyMany(Clause* c);
    Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }

  private:
    struct ProxyEliminationIterator;
    struct ProxyEliminationFn;

};*/


}

#endif
