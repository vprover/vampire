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
 * @file Subterm.cpp
 * Inferences about a subterm relation
 */

#include "Subterm.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"

using Kernel::Clause;
using Kernel::Interpretation;
using Kernel::Theory;
using Symbol = Kernel::Signature::Symbol;
using InterpretedSymbol = Kernel::Signature::InterpretedSymbol;

namespace Inferences {

void SubtermGIE::attach(SaturationAlgorithm *salg)
{
  CALL("SubtermGIE::attach")
  GeneratingInferenceEngine::attach(salg);
}

void SubtermGIE::detach()
{
  CALL("SubtermGIE::detach")
  GeneratingInferenceEngine::detach();
}

static bool is_subterm_literal(Literal *l) {
  unsigned functor = l->functor();
  Symbol *symbol = env.signature->getPredicate(functor);
  if (!symbol->interpreted())
    return false;

  InterpretedSymbol *interpreted = static_cast<InterpretedSymbol *>(symbol);
  Interpretation itp = interpreted->getInterpretation();
  if (itp != Theory::SUBTERM)
    return false;

  TermList rhs = (*l)[1];
  if(!rhs.isTerm())
    return false;

  Term *superterm = rhs.term();
  return env.signature->getFunction(superterm->functor())->termAlgebraCons();
}

static Clause *replaceLiteral(Clause *premise, Literal *remove, Literal *add, const Inference &inference) {
  Clause *generated = new (premise->length()) Clause(premise->length(), inference);
  for (unsigned i = 0; i < premise->length(); i++)
    (*generated)[i] = (*premise)[i] == remove ? add : (*premise)[i];
  return generated;
}

static ClauseIterator perform(Clause *premise, Literal *selected) {
  CALL("SubtermGIE::perform")

  unsigned functor = selected->functor();
  TermList sort = env.signature->getFunction(functor)->predType()->arg(0);
  TermList lhs = (*selected)[0];
  TermList rhs = (*selected)[1];
  Term *superterm = rhs.term();
  unsigned super_arity = superterm->arity();

  if (selected->isPositive()) {
    Inference inference(GeneratingInference1(InferenceRule::POSITIVE_SUBTERM, premise));
    unsigned length = premise->length() + super_arity;
    Clause *generated = new (length) Clause(length, inference);

    (*generated)[0] = Literal::createEquality(true, lhs, rhs, sort);
    for (unsigned i = 0; i < super_arity; i++)
      (*generated)[i + 1] = Literal::create2(functor, true, lhs, (*superterm)[i]);

    unsigned j = super_arity;
    for (unsigned i = 0; i < premise->length(); i++)
      if ((*premise)[i] != selected)
        (*generated)[j++] = (*premise)[i];

    return pvi(getSingletonIterator(generated));
  }
  else {
    Inference inference(GeneratingInference1(InferenceRule::NEGATIVE_SUBTERM, premise));
    auto equality_clause = getSingletonIterator(replaceLiteral(
      premise,
      selected,
      Literal::createEquality(false, lhs, rhs, sort),
      inference
    ));

    Term::Iterator arguments(superterm);
    auto subterm_clauses = getMappingIterator(arguments, [=](TermList argument) {
      Literal *subterm = Literal::create2(functor, false, lhs, argument);
      return replaceLiteral(premise, selected, subterm, inference);
    });

    return pvi(getConcatenatedIterator(equality_clause, subterm_clauses));
  }
}

ClauseIterator SubtermGIE::generateClauses(Clause *premise) {
  CALL("SubtermGIE::generateClauses")

  auto selected = premise->getSelectedLiteralIterator();
  auto filtered = getFilteredIterator(selected, is_subterm_literal);
  auto mapped = getMapAndFlattenIterator(filtered, [premise](Literal *l) {
    return perform(premise, l);
  });
  return pvi(mapped);
}

} // namespace Inferences