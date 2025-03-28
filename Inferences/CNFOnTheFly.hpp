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
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

#include <memory>

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
  ClauseIterator simplifyMany(Clause* c) override;
  Clause* simplify(Clause* c) override { NOT_IMPLEMENTED; }

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

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }

private:
  SkolemisingFormulaIndex* _formulaIndex;
};

/*class NotProxyISE
  : public ImmediateSimplificationEngine
{
public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};


class EqualsProxyISE
   : public ImmediateSimplificationEngine
{

public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};


class OrImpAndProxyISE
  : public ImmediateSimplificationEngine
{

public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};


class PiSigmaProxyISE
   : public ImmediateSimplificationEngine
{
  
public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};


class ProxyISE 
  : public ImmediateSimplificationEngine {
  public:
    ClauseIterator simplifyMany(Clause* c) override;
    Clause* simplify(Clause* c){ NOT_IMPLEMENTED; }
};*/


}

#endif
