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

#include "CCSA.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

using Kernel::Clause;
using Kernel::Interpretation;
using Kernel::SortHelper;
using Kernel::Theory;
using Symbol = Kernel::Signature::Symbol;
using InterpretedSymbol = Kernel::Signature::InterpretedSymbol;
using TermSubstitutionTree = Indexing::TermSubstitutionTree;
using LiteralSubstitutionTree = Indexing::LiteralSubstitutionTree;
using TermQueryResultIterator = Indexing::TermQueryResultIterator;
using TermQueryResult = Indexing::TermQueryResult;
using LiteralQueryResultIterator = Indexing::SLQueryResultIterator;
using LiteralQueryResult = Indexing::SLQueryResult;
using LeafData = Indexing::SubstitutionTree::LeafData;

namespace Inferences {

static DHSet<std::pair<unsigned, unsigned>> commutes;

void SubtermGIE::registerCommutes(unsigned relation, unsigned functor) {
  CALL("SubtermGIE::registerCommutes");
  commutes.insert(std::make_pair(relation, functor));
}

static bool isInterestingSubterm(Literal *l) {
  unsigned functor = l->functor();
  Symbol *symbol = env.signature->getPredicate(functor);
  if (!symbol->interpreted())
    return false;

  InterpretedSymbol *interpreted = static_cast<InterpretedSymbol *>(symbol);
  Interpretation itp = interpreted->getInterpretation();
  if (itp != Theory::SUBTERM)
    return false;

  TermList rhs = (*l)[2];
  if(!rhs.isTerm())
    return false;

  TermList rel = (*l)[0];
  if(!rel.isTerm())
    return false;

  return commutes.contains(std::make_pair(rel.term()->functor(), rhs.term()->functor()));
}

static Clause *replaceLiteral(Clause *premise, Literal *remove, Literal *add, const Inference &inference) {
  Clause *generated = new (premise->length()) Clause(premise->length(), inference);
  for (unsigned i = 0; i < premise->length(); i++)
    (*generated)[i] = (*premise)[i] == remove ? add : (*premise)[i];
  return generated;
}

static ClauseIterator perform(Clause *premise, Literal *selected) {
  CALL("SubtermGIE::perform")

  TermList relation = (*selected)[0];
  TermList subterm = (*selected)[1];
  TermList subterm_sort = SortHelper::getArgSort(selected, 1);
  TermList superterm = (*selected)[2];
  Term *super = superterm.term();
  TermList superterm_sort = SortHelper::getArgSort(selected, 2);
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
        relation,
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
      [premise, selected, inference, relation, subterm, subterm_sort, super](unsigned i) {
        Literal *new_subterm = SubtermGIE::createSubterm(
          false,
          relation,
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
  auto filtered = getFilteredIterator(selected, isInterestingSubterm);
  auto mapped = getMapAndFlattenIterator(filtered, [premise](Literal *l) {
    return perform(premise, l);
  });
  return pvi(mapped);
}

Literal *SubtermGIE::createSubterm(
  bool polarity,
  TermList relation,
  TermList subterm,
  TermList subterm_sort,
  TermList superterm,
  TermList superterm_sort
) {
  CALL("SubtermGIE::createSubterm")
  unsigned predicate = env.signature->getInterpretingSymbol(
    Theory::SUBTERM,
    OperatorType::getPredicateType({AtomicSort::defaultSort(), subterm_sort, superterm_sort})
  );
  return Literal::create(predicate, polarity, {relation, subterm, superterm});
}

static TermSubstitutionTree term_index;
static DHMap<TermList, TermList> term_map;

void RewriteGIE::registerTermRewrite(TermList left, TermList right) {
  CALL("RewriteGIE::registerRewrite")
  term_index.insert(left, nullptr, nullptr);
  term_map.insert(left, right);
}

static LiteralSubstitutionTree literal_index;
static DHMap<Literal *, Literal *> literal_map;

void RewriteGIE::registerLiteralRewrite(Literal *left, Literal *right) {
  CALL("RewriteGIE::registerRewrite")
  literal_index.insert(left, nullptr);
  literal_map.insert(left, right);
}

ClauseIterator RewriteGIE::generateClauses(Clause *cl) {
  CALL("RewriteGIE::generateClauses")

  static ClauseStack results;
  results.reset();

  for(unsigned i = 0; i < cl->length(); i++) {
    Literal *literal = cl->literals()[i];

    LiteralQueryResultIterator literal_results = literal_index.getGeneralizations(literal, false, true);
    if(literal_results.hasNext()) {
      LiteralQueryResult result = literal_results.next();
      Literal *rewritten = result.substitution->applyToBoundResult(literal_map.get(result.literal));

      Inference inference(GeneratingInference1(InferenceRule::REWRITE, cl));
      results.push(replaceLiteral(cl, literal, rewritten, inference));
    }

    NonVariableNonTypeIterator subterms(literal);
    while(subterms.hasNext()) {
      TermList subterm = subterms.next();
      TermQueryResultIterator term_results = term_index.getGeneralizations(subterm, true);
      if(!term_results.hasNext())
        continue;

      TermQueryResult result = term_results.next();
      TermList rhs = result.substitution->applyToBoundResult(term_map.get(result.term));
      Literal *rewritten = EqHelper::replace(literal, subterm, rhs);

      Inference inference(SimplifyingInference1(InferenceRule::REWRITE, cl));
      results.push(replaceLiteral(cl, literal, rewritten, inference));
    }
  }

  ClauseStack::BottomFirstIterator it(results);
  return pvi(it);
}

} // namespace Inferences
