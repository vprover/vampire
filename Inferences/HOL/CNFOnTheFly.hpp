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
#include "Inferences/InferenceEngine.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
using namespace Indexing;

namespace Inferences {

class SkolemisingFormulaIndex
{
public:
  void insertFormula(TermList formula, TermList skolem) {
    _ct.insert(TermWithValue<TermList>(TypedTermList(formula.term()), skolem));
  }
  auto getSkolem(Term* forTerm) {
    return _ct.getGeneralizations(TypedTermList(forTerm), true);
  }
private:
  CodeTreeTIS<true, TermWithValue<TermList>> _ct;
};

class IFFXORRewriterISE
  : public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* c) override;
};

class EagerClausificationISE
  : public ImmediateSimplificationEngineMany
{
public:
  Option<ClauseIterator> simplifyMany(Clause* c) override;
};

class LazyClausification
  : public SimplificationEngine
{
public:
  LazyClausification(SaturationAlgorithm&) {}
  ClauseIterator perform(Clause* c) override;
private:
  SkolemisingFormulaIndex _formulaIndex;
};

class LazyClausificationGIE
  : public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* c) override;

private:
  SkolemisingFormulaIndex _formulaIndex;
};

}

#endif
