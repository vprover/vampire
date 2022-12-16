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
namespace CCSA {

static DHSet<std::pair<unsigned, unsigned>> commutes;

void registerCommutes(unsigned relation, unsigned functor) {
  CALL("CCSA::registerCommutes");
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

static Clause *replaceLiteral(Clause *premise, Literal *remove, Stack<Literal *> add, const Inference &inference) {
  unsigned length = premise->length() + add.length() - 1;
  Clause *generated = new (length) Clause(length, inference);

  unsigned index = 0;
  for (unsigned i = 0; i < premise->length(); i++)
    if((*premise)[i] != remove)
      (*generated)[index++] = (*premise)[i];
  while(add.isNonEmpty())
    (*generated)[index++] = add.pop();

  return generated;
}

static ClauseIterator perform(Clause *premise, Literal *literal) {
  CALL("SubtermISE::perform")

  TermList relation = (*literal)[0];
  TermList subterm = (*literal)[1];
  TermList subterm_sort = SortHelper::getArgSort(literal, 1);
  TermList superterm = (*literal)[2];
  Term *super = superterm.term();
  TermList superterm_sort = SortHelper::getArgSort(literal, 2);
  unsigned super_args = super->numTermArguments();

  bool equality_would_be_wellsorted = subterm_sort == superterm_sort;

  if (literal->isPositive()) {
    Inference inference(SimplifyingInference1(InferenceRule::POSITIVE_SUBTERM, premise));
    unsigned length = premise->length() - 1 + super_args + equality_would_be_wellsorted;
    Clause *generated = new (length) Clause(length, inference);

    unsigned j = 0;
    for (unsigned i = 0; i < premise->length(); i++)
      if ((*premise)[i] != literal)
        (*generated)[j++] = (*premise)[i];

    for (unsigned i = 0; i < super_args; i++)
      (*generated)[j++] = createSubterm(
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
    auto subterm_clauses = getMappingIterator(
      getRangeIterator(0u, super_args),
      [premise, literal, relation, subterm, subterm_sort, super](unsigned i) {
        Literal *new_subterm = createSubterm(
          false,
          relation,
          subterm,
          subterm_sort,
          super->termArg(i),
          SortHelper::getArgSort(super, super->numTypeArguments() + i)
        );
        Inference inference(SimplifyingInference1(InferenceRule::NEGATIVE_SUBTERM, premise));
        return replaceLiteral(premise, literal, new_subterm, inference);
      }
    );

    if(equality_would_be_wellsorted) {
      auto equality_clause = getSingletonIterator(replaceLiteral(
        premise,
        literal,
        Literal::createEquality(false, subterm, superterm, subterm_sort),
        SimplifyingInference1(InferenceRule::NEGATIVE_SUBTERM, premise)
      ));
      return pvi(getConcatenatedIterator(equality_clause, subterm_clauses));
    }

    return pvi(subterm_clauses);
  }
}

ClauseIterator SubtermISE::simplifyMany(Clause* premise) {
  CALL("SubtermISE::simplifyMany")

  for(unsigned i = 0; i < premise->length(); i++)
    if(isInterestingSubterm((*premise)[i]))
      return perform(premise, (*premise)[i]);

  return ClauseIterator::getEmpty();
}

Literal *createSubterm(
  bool polarity,
  TermList relation,
  TermList subterm,
  TermList subterm_sort,
  TermList superterm,
  TermList superterm_sort
) {
  CALL("CCSA::createSubterm")
  unsigned predicate = env.signature->getInterpretingSymbol(
    Theory::SUBTERM,
    OperatorType::getPredicateType({AtomicSort::defaultSort(), subterm_sort, superterm_sort})
  );
  return Literal::create(predicate, polarity, {relation, subterm, superterm});
}

static TermSubstitutionTree term_index;
static DHMap<TermList, TermList> term_map;

void registerTermRewrite(TermList left, TermList right) {
  CALL("CCSA::registerTermRewrite")
  term_index.insert(left, nullptr, nullptr);
  term_map.insert(left, right);
}

static LiteralSubstitutionTree literal_index;
static DHMap<Literal *, Stack<Stack<Literal *>>> literal_map;

void registerLiteralRewrite(Literal *left, Stack<Stack<Literal *>> right) {
  CALL("CCSA::registerLiteralRewrite")
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
      const Stack<Stack<Literal *>> &conjunction = literal_map.get(result.literal);
      Stack<Stack<Literal *>>::ConstIterator disjunctions(conjunction);

      while(disjunctions.hasNext()) {
        const Stack<Literal *> &disjunction = disjunctions.next();
        Stack<Literal *>::ConstIterator literals(disjunction);
        Stack<Literal *> rewritten;
        while(literals.hasNext())
          rewritten.push(result.substitution->applyToBoundResult(literals.next()));

        Inference inference(GeneratingInference1(InferenceRule::REWRITE, cl));
        results.push(replaceLiteral(cl, literal, rewritten, inference));
      }
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

      Inference inference(GeneratingInference1(InferenceRule::REWRITE, cl));
      results.push(replaceLiteral(cl, literal, rewritten, inference));
    }
  }

  ClauseStack::BottomFirstIterator it(results);
  return pvi(it);
}

} // namespace CCSA
} // namespace Inferences
