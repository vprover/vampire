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
#include "Kernel/TermTransformer.hpp"

#include "InferenceEngine.hpp"

#include "Lib/DHMap.hpp"


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

class MultiTermReplacement : public TermTransformer 
{
public:
  MultiTermReplacement(DHMap<TermList, pair<TermList, TermList>>* rewrites,
  	TermList* maxNlIntroduced) : 
  _rewrites(rewrites), _maxNl(maxNlIntroduced) {} 
  virtual TermList transformSubterm(TermList trm);
private:
  DHMap<TermList, pair<TermList, TermList>>* _rewrites;
  TermList* _maxNl;
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
  Clause* rewriteClause(Clause* c, TermList toBeReplaced, TermList replacement);
  Clause* rewriteClause(Clause* c, TermList& maxNlIntroduced);
  void createConclusions(ClauseStack& premises, TermList nlTerm, 
  	                     ClauseStack& concs,  bool multiLiterals, bool allGround);
  bool ground(Clause* c);

  MultiClauseNatInductionIndex* _index;  
  DHMap<TermList, pair<TermList, TermList>> _rewriteRules;
};


};

#endif /* __PrimitiveInstantiation__ */
