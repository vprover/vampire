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
 * @file DelayedUnification.cpp
 * Things for Ahmed/Joe's delayed-unification CADE '23 calculus
 */

#include "DelayedUnification.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Indexing/IndexManager.hpp"
#include "Lib/Metaiterators.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

void DelayedSubterms::handleClause(Clause *c, bool adding) {
  CALL("DelayedSubterms::handleClause")

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator subterms(EqHelper::getSubtermIterator(lit, _ordering));
    while (subterms.hasNext())
      handle(c, lit, subterms.next().term(), adding);
  }
}

void DelayedLHS::handleClause(Clause *c, bool adding) {
  CALL("DelayedLHS::handleClause")

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator lhs(EqHelper::getSuperpositionLHSIterator(lit, _ordering, _options));
    while (lhs.hasNext()) {
      TermList next = lhs.next();
      if(next.isTerm())
        handle(c, lit, next.term(), adding);
      else if(adding)
        _variables.insert({c, lit, next});
      else
        _variables.remove({c, lit, next});
    }
  }
}


void DelayedSuperposition::attach(SaturationAlgorithm *salg) {
  CALL("DelayedSuperposition::attach")
  GeneratingInferenceEngine::attach(salg);
  _subtermIndex = static_cast<DelayedSubterms *>(salg->getIndexManager()->request(DELAYED_SUBTERMS));
  _lhsIndex = static_cast<DelayedLHS *>(salg->getIndexManager()->request(DELAYED_EQUATIONS));
}

Clause *DelayedSuperposition::perform(
  Clause *equationClause,
  Literal *equation,
  TermList lhs,
  Clause *subtermClause,
  Literal *subtermLiteral,
  Term *subterm
) {
  CALL("DelayedSuperposition::perform")

  // prevent self-superposition l = r in l = r to get r = r, which seems to happen a surprising amount
  if(equationClause == subtermClause && equation == subtermLiteral && TermList(subterm) == lhs)
    return nullptr;

  // TODO if lhs is a var, check that the rewrite is well-sorted
  // TODO if lhs is a var, call checkSuperpositionFromVariable?

  TermList rhs = EqHelper::getOtherEqualitySide(equation, lhs);

  // compute a renaming for both clauses so that variables are disjoint
  Renaming equationRenaming;
  for(unsigned i = 0; i < equationClause->length(); i++)
    equationRenaming.normalizeVariables((*equationClause)[i]);

  Renaming subtermRenaming(equationClause->varCnt());
  for(unsigned i = 0; i < subtermClause->length(); i++)
    subtermRenaming.normalizeVariables((*subtermClause)[i]);

  // some helpfully-renamed terms
  TermList lhs_renamed = equationRenaming.apply(lhs);
  TermList rhs_renamed = equationRenaming.apply(rhs);
  Term *subterm_renamed = subtermRenaming.apply(subterm);

  // if lhs is a var, check subterm > rhs
  if(lhs.isVar() && Ordering::isGorGEorE(_salg->getOrdering().compare(rhs_renamed, TermList(subterm_renamed))))
    return nullptr;

  // TODO check whether we are rewriting smaller side of equation? superposition checks this here

  // the rewritten literal
  Literal *rewritten = EqHelper::replace(
    subtermRenaming.apply(subtermLiteral),
    TermList(subterm_renamed),
    equationRenaming.apply(rhs)
  );
  if(EqHelper::isEqTautology(rewritten))
    return nullptr;

  // compute clause length and create a blank clause to fill
  unsigned arity = lhs.isVar() ? 0 : lhs.term()->arity();
  unsigned length = equationClause->length() + subtermClause->length() + arity - 1;
  Inference inference(GeneratingInference2(
    InferenceRule::DELAYED_SUPERPOSITION,
    equationClause,
    subtermClause
  ));
  Clause *cl = new (length) Clause(length, inference);

  // how far are we through the clause?
  unsigned i = 0;

  // copy side literals into new clause from old, applying the renaming
  for(unsigned j = 0; j < equationClause->length(); j++)
    if((*equationClause)[j] != equation)
      (*cl)[i++] = equationRenaming.apply((*equationClause)[j]);
  for(unsigned j = 0; j < subtermClause->length(); j++)
    if((*subtermClause)[j] != subtermLiteral)
      (*cl)[i++] = subtermRenaming.apply((*subtermClause)[j]);

  // add rewritten literal
  (*cl)[i++] = rewritten;

  if(lhs.isTerm()) {
    Term *lhs_renamed_term = lhs_renamed.term();
    ASS_EQ(lhs_renamed_term->functor(), subterm_renamed->functor())

    // create disequations
    for(unsigned j = 0; j < arity; j++) {
      TermList larg = (*lhs_renamed_term)[j];
      TermList rarg = (*subterm_renamed)[j];
      // TODO deal with polymorphic sorts properly: this will work until it doesn't
      TermList sort = SortHelper::getArgSort(subterm_renamed, j);
      Literal *disequation = Literal::createEquality(false, larg, rarg, sort);
      (*cl)[i++] = disequation;
    }
  }
  else {
    ASS(lhs_renamed.isVar())

    // apply substitution of lhs -> subterm
    // OK to do this as a naive replacement because of single binding with disjoint variables
    for(unsigned i = 0; i < cl->length(); i++)
      (*cl)[i] = EqHelper::replace(
        (*cl)[i],
        lhs_renamed,
        TermList(subterm_renamed)
      );

    // TODO check literals are still maximal under substitution?
  }

  /*
  std::cout << equationClause->toString() << std::endl;
  std::cout << lhs.toString() << " -> " << rhs.toString() << std::endl;
  std::cout << subtermClause->toString() << std::endl;
  std::cout << subtermLiteral->toString() << std::endl;
  std::cout << subterm->toString() << std::endl;
  std::cout << cl->toString() << std::endl;
  std::cout << "-----------------------------" << std::endl;
  */
  return cl;
}

ClauseIterator DelayedSuperposition::generateClauses(Clause *cl) {
  CALL("DelayedSuperposition::generateClauses")

  typedef TopSymbolIndex::Entry<Term *> TEntry;
  typedef TopSymbolIndex::Entry<TermList> TLEntry;
  typedef std::pair<TLEntry, TEntry> Superposition;

  // selected literals
  auto fwselected = cl->getSelectedLiteralIterator();

  // rewritable subterms of selected literals
  auto fwsubterms = getMapAndFlattenIterator(fwselected, [this, cl](Literal *lit) {
    // TODO avoid boxing here? should not be necessary, but there are some move-semantic errors
    return pvi(getMappingIterator(
      EqHelper::getSubtermIterator(lit, _salg->getOrdering()),
      [lit, cl](TermList term) -> TEntry { return { cl, lit, term.term() }; }
    ));
  });

  // forward superpositions
  auto fwsuperpositions = getMapAndFlattenIterator(fwsubterms, [this](TEntry subterm) {
    return pvi(getMappingIterator(
      getConcatenatedIterator(
        getMappingIterator(
          _lhsIndex->query(subterm.term->functor()),
          [](TEntry entry) { return entry.termList(); }
        ),
        _lhsIndex->variables()
      ),
      [subterm](TLEntry rewrite) -> Superposition { return { rewrite, subterm }; }
    ));
  });

  // selected literals
  auto bwselected = cl->getSelectedLiteralIterator();

  // oriented equations in selected literals
  auto bwrewrites = getMapAndFlattenIterator(bwselected, [this, cl](Literal *lit) {
    return pvi(getMappingIterator(
      EqHelper::getSuperpositionLHSIterator(lit, _salg->getOrdering(), _salg->getOptions()),
      [cl, lit](TermList lhs) -> TLEntry { return { cl, lit, lhs }; }
    ));
  });

  // backward superpositions
  auto bwsuperpositions = getMapAndFlattenIterator(bwrewrites, [this](TLEntry rewrite) {
    return pvi(getMappingIterator(
      rewrite.term.isVar()
        ? _subtermIndex->entries()
        : _subtermIndex->query(rewrite.term.term()->functor()),
      [rewrite](TEntry subterm) -> Superposition { return { rewrite, subterm }; }
    ));
  });

  // fw + bw superpositions
  auto superpositions = getConcatenatedIterator(fwsuperpositions, bwsuperpositions);

  // all resulting superposition attempts
  auto attempts = getMappingIterator(superpositions, [this](Superposition superposition) {
    TLEntry rewrite = superposition.first;
    TEntry subterm = superposition.second;
    return perform(
      rewrite.clause,
      rewrite.literal,
      rewrite.term,
      subterm.clause,
      subterm.literal,
      subterm.term
    );
  });

  return pvi(getFilteredIterator(attempts, [](Clause *cl) { return cl; }));
}

} //namespace Inferences
