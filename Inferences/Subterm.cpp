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
#include "Kernel/SortHelper.hpp"

using Kernel::Clause;
using Kernel::Interpretation;
using Kernel::SortHelper;
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

static bool filter(Literal *l) {
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

  TermList subterm = (*selected)[0];
  TermList subterm_sort = SortHelper::getArgSort(selected, 0);
  TermList superterm = (*selected)[1];
  Term *super = superterm.term();
  TermList superterm_sort = SortHelper::getArgSort(selected, 1);
  unsigned super_args = super->numTermArguments();

  bool equality_would_be_wellsorted = subterm_sort == superterm_sort;

  if (selected->isPositive()) {
    Inference inference(GeneratingInference1(InferenceRule::POSITIVE_SUBTERM, premise));
    unsigned length = premise->length() - 1 + super_args + equality_would_be_wellsorted;
    Clause *generated = new (length) Clause(length, inference);

    unsigned j = 0;
    for (unsigned i = 0; i < premise->length(); i++)
      if ((*premise)[i] != selected)
        (*generated)[j++] = (*premise)[i];

    for (unsigned i = 0; i < super_args; i++)
      (*generated)[j++] = SubtermGIE::createSubterm(
        true,
        subterm,
        subterm_sort,
        super->termArg(i),
        SortHelper::getArgSort(super, super->numTypeArguments() + i)
      );

    if(equality_would_be_wellsorted)
      (*generated)[j++] = Literal::createEquality(true, subterm, superterm, subterm_sort);

    ASS_EQ(j, length);
    return pvi(getSingletonIterator(generated));
  }
  else {
    Inference inference(GeneratingInference1(InferenceRule::NEGATIVE_SUBTERM, premise));
    auto subterm_clauses = getMappingIterator(
      getRangeIterator(0u, super_args),
      [premise, selected, inference, subterm, subterm_sort, super](unsigned i) {
        Literal *new_subterm = SubtermGIE::createSubterm(
          false,
          subterm,
          subterm_sort,
          super->termArg(i),
          SortHelper::getArgSort(super, super->numTypeArguments() + i)
        );
        return replaceLiteral(premise, selected, new_subterm, inference);
      }
    );

    if(equality_would_be_wellsorted) {
      auto equality_clause = getSingletonIterator(replaceLiteral(
        premise,
        selected,
        Literal::createEquality(false, subterm, superterm, subterm_sort),
        inference
      ));
      return pvi(getConcatenatedIterator(equality_clause, subterm_clauses));
    }

    return pvi(subterm_clauses);
  }
}

ClauseIterator SubtermGIE::generateClauses(Clause *premise) {
  CALL("SubtermGIE::generateClauses")

  auto selected = premise->getSelectedLiteralIterator();
  auto filtered = getFilteredIterator(selected, filter);
  auto mapped = getMapAndFlattenIterator(filtered, [premise](Literal *l) {
    return perform(premise, l);
  });
  return pvi(mapped);
}

Literal *SubtermGIE::createSubterm(
  bool polarity,
  TermList subterm,
  TermList subterm_sort,
  TermList superterm,
  TermList superterm_sort
) {
  CALL("SubtermGIE::createSubterm")
  unsigned predicate = env.signature->getInterpretingSymbol(
    Theory::SUBTERM,
    OperatorType::getPredicateType({subterm_sort, superterm_sort})
  );
  return Literal::create2(predicate, polarity, subterm, superterm);
}

} // namespace Inferences