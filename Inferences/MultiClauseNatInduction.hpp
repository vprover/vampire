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
 * @file PrimitiveInstantiation.hpp
 * Defines class PrimitiveInstantiation.
 */


#ifndef __MultiClauseNatInduction__
#define __MultiClauseNatInduction__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/FormulaTransformer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TermReplacingFormulaTransformer : public FormulaTransformer
{
public:
  TermReplacingFormulaTransformer(TermList t1, TermList t2) 
  : _toBeReplaced(t1), _replacer(t2) {}
protected:
  virtual Formula* applyLiteral(Formula* f);

private:
  TermList _toBeReplaced;
  TermList _replacer;
};

class MultiClauseNatInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(MultiClauseNatInduction);
  USE_ALLOCATOR(MultiClauseNatInduction);
 
  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);
  
private:
  void createConclusions(ClauseStack& premises, TermList nlTerm, ClauseStack& concs,  bool multiLiterals);

  MultiClauseNatInductionIndex* _index;  

};


};

#endif /* __PrimitiveInstantiation__ */
