/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ProxyElimination.hpp
 * Defines class ProxyElimination.
 */

#ifndef __CNFOnTheFly__
#define __CNFOnTheFly__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {
using namespace Indexing;

class IFFXORRewriterISE
  : public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* c) override;
};

class EagerClausificationISE
  : public ImmediateSimplificationEngine
{
public:
  ClauseIterator simplifyMany(Clause* c);
  Clause* simplify(Clause* c) override{ NOT_IMPLEMENTED; }

};

class LazyClausification
  : public SimplificationEngine
{
public:
  LazyClausification(){
    _formulaIndex = 0;
  }

  ClauseIterator perform(Clause* c) override;

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

class LazyClausificationGIE
  : public GeneratingInferenceEngine
{
public:
  LazyClausificationGIE(){
    _formulaIndex = 0;
  }

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* c) override;

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

/*class NotProxyISE
  : public ImmediateSimplificationEngine
{
public:
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class EqualsProxyISE
   : public ImmediateSimplificationEngine
{

public:
  Kernel::Clause* simplify(Kernel::Clause* c);        
};


class OrImpAndProxyISE
  : public ImmediateSimplificationEngine
{

public:
  Kernel::Clause* simplify(Kernel::Clause* c);
};


class PiSigmaProxyISE
   : public ImmediateSimplificationEngine
{
  
public:
  Kernel::Clause* simplify(Kernel::Clause* c);     
};


class ProxyISE 
  : public ImmediateSimplificationEngine {
  public:
    ClauseIterator simplifyMany(Clause* c);
    Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }
};*/


}

#endif
