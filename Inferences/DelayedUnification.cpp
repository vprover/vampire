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

static Clause *delayed_superposition(
  Clause *equationClause,
  Literal *equation,
  TermList lhs,
  Clause *subtermClause,
  Literal *subtermLiteral,
  Term *rewritten
) {
  CALL("delayed_superposition")

  // prevent self-superposition l = r in l = r to get r = r, which seems to happen a surprising amount
  if(equationClause == subtermClause && equation == subtermLiteral && TermList(rewritten) == lhs)
    return nullptr;

  std::cout << equationClause->toString() << std::endl;
  std::cout << equation->toString() << std::endl;
  std::cout << lhs.toString() << std::endl;
  std::cout << subtermClause->toString() << std::endl;
  std::cout << subtermLiteral->toString() << std::endl;
  std::cout << rewritten->toString() << std::endl;

  Inference inference(GeneratingInference2(
    InferenceRule::DELAYED_SUPERPOSITION,
    equationClause,
    subtermClause
  ));

  Renaming subtermRenaming;
  Renaming equationRenaming(subtermClause->varCnt());

  unsigned arity = lhs.isVar() ? 0 : lhs.term()->arity();
  unsigned length = equationClause->length() + subtermClause->length() + arity - 1;
  Clause *cl = new (length) Clause(length, inference);

  unsigned i = 0;

  // copy literals into new clause from old
  for(unsigned j = 0; j < subtermClause->length(); j++)
    if((*subtermClause)[j] != subtermLiteral)
      (*cl)[i++] = subtermRenaming.apply((*subtermClause)[j]);
  for(unsigned j = 0; j < equationClause->length(); j++)
    if((*equationClause)[j] != equation)
      (*cl)[i++] = equationRenaming.apply((*equationClause)[j]);

  // the rewritten literal
  (*cl)[i++] = EqHelper::replace(
    subtermRenaming.apply(subtermLiteral),
    TermList(subtermRenaming.apply(rewritten)),
    TermList(equationRenaming.apply((*equation)[0] == lhs ? (*equation)[1] : (*equation)[0]))
  );

  if(lhs.isTerm()) {
    Term *lhst = lhs.term();
    ASS_EQ(lhst->functor(), rewritten->functor())

    // create disequations
    for(unsigned j = 0; j < arity; j++) {
      TermList larg = equationRenaming.apply((*lhst)[j]);
      TermList rarg = subtermRenaming.apply((*rewritten)[j]);
      // TODO deal with polymorphic sorts properly: this will work until it doesn't
      TermList sort = SortHelper::getArgSort(rewritten, j);
      Literal *disequation = Literal::createEquality(false, larg, rarg, sort);
      (*cl)[i++] = disequation;
    }

  }
  else {
    NOT_IMPLEMENTED;
  }

  std::cout << cl->toString() << std::endl;
  std::cout << "-----------------------------" << std::endl;
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
      _lhsIndex->query(subterm.term->functor()),
      [subterm](TEntry entry) -> Superposition { return { entry.termList(), subterm }; }
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
      _subtermIndex->query(rewrite.term.term()->functor()),
      [rewrite](TEntry subterm) -> Superposition { return { rewrite, subterm }; }
    ));
  });

  // fw + bw superpositions
  auto superpositions = getConcatenatedIterator(fwsuperpositions, bwsuperpositions);

  // all resulting superposition attempts
  auto attempts = getMappingIterator(superpositions, [](Superposition superposition) {
    TLEntry rewrite = superposition.first;
    TEntry subterm = superposition.second;
    return delayed_superposition(
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
