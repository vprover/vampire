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
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

void TopSymbolIndex::handle(unsigned functor, Clause *c, Literal *lit, bool adding) {
  CALL("TopSymbolIndex::handle")
  typedef std::pair<Clause *, Literal *> Entry;
  typedef DHSet<Entry> Entries;

  Entries **entriesPtr;
  _functors.getValuePtr(functor, entriesPtr, nullptr);
  if(!*entriesPtr)
    *entriesPtr = new Entries();
  Entries *entries = *entriesPtr;

  if(adding)
    entries->insert({c, lit});
  else
    entries->remove({c, lit});
}

void DelayedSubterms::handleClause(Clause *c, bool adding) {
  CALL("DUSubterms::handleClause")

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator subterms(EqHelper::getSubtermIterator(lit, _ordering));
    while (subterms.hasNext())
      handle(subterms.next().term()->functor(), c, lit, adding);
  }
}

void DelayedLHS::handleClause(Clause *c, bool adding) {
  CALL("DULHS::handleClause")

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator lhss(EqHelper::getSuperpositionLHSIterator(lit, _ordering, _options));
    while (lhss.hasNext())
      handle(lhss.next().term()->functor(), c, lit, adding);
  }
}


void DelayedSuperposition::attach(SaturationAlgorithm *salg) {
  CALL("DelayedSuperposition::attach")
  GeneratingInferenceEngine::attach(salg);
  _subtermIndex = static_cast<DelayedSubterms *>(salg->getIndexManager()->request(DELAYED_SUBTERMS));
  _lhsIndex = static_cast<DelayedLHS *>(salg->getIndexManager()->request(DELAYED_EQUATIONS));
}

static Clause *superposition(
  Clause *equationClause,
  Literal *equation,
  TermList lhs,
  Clause *subtermClause,
  Literal *subtermLiteral,
  Term *rewritten
) {
  CALL("DelayedSuperposition::superposition")

  // prevent self-superposition l = r in l = r to get r = r, which seems to happen a surprising amount
  if(equationClause == subtermClause && equation == subtermLiteral && TermList(rewritten) == lhs)
    return nullptr;

  std::cout << equationClause->toString() << std::endl;
  std::cout << equation->toString() << std::endl;
  std::cout << lhs.toString() << std::endl;
  std::cout << subtermClause->toString() << std::endl;
  std::cout << subtermLiteral->toString() << std::endl;
  std::cout << rewritten->toString() << std::endl;
  std::cout << "-----------------------------" << std::endl;

  Inference inf(GeneratingInference2(InferenceRule::SUPERPOSITION, equationClause, subtermClause));
  Clause *cl = nullptr;

  Renaming subtermRenaming;
  Renaming equationRenaming(subtermClause->varCnt());

  if(lhs.isTerm()) {
    Term *lhst = lhs.term();
    ASS_EQ(lhst->functor(), rewritten->functor())
    unsigned arity = rewritten->arity();
    unsigned length = equationClause->length() + subtermClause->length() + arity - 1;
    cl = new (length) Clause(length, inf);
    unsigned i = 0;

    // copy literals into new clause from old
    for(unsigned j = 0; j < subtermClause->length(); j++)
      if((*subtermClause)[j] != subtermLiteral)
        (*cl)[i++] = subtermRenaming.apply((*subtermClause)[j]);
    for(unsigned j = 0; j < equationClause->length(); j++)
      if((*equationClause)[j] != equation)
        (*cl)[i++] = equationRenaming.apply((*equationClause)[j]);

    // create disequations
    for(unsigned j = 0; j < arity; j++) {
      TermList larg = equationRenaming.apply((*lhst)[j]);
      TermList rarg = subtermRenaming.apply((*rewritten)[j]);
      // TODO deal with polymorphic sorts properly: this will work until it doesn't
      TermList sort = SortHelper::getArgSort(rewritten, j);
      Literal *disequation = Literal::createEquality(false, larg, rarg, sort);
      (*cl)[i++] = disequation;
    }

    // the rewritten literal
    (*cl)[i++] = EqHelper::replace(
      subtermRenaming.apply(subtermLiteral),
      TermList(subtermRenaming.apply(rewritten)),
      TermList(equationRenaming.apply((*equation)[0] == lhs ? (*equation)[1] : (*equation)[0]))
    );
  }
  else {
    NOT_IMPLEMENTED;
  }

  std::cout << "produced: " << cl->toString() << std::endl;
  return cl;
}

ClauseIterator DelayedSuperposition::generateClauses(Clause *cl) {
  CALL("DelayedSuperposition::generateClauses")

  typedef std::pair<Literal *, Term *> Rewritable;
  typedef std::pair<Clause *, Literal *> Equation;
  typedef std::pair<Equation, TermList> Rewrite;
  typedef std::pair<Rewritable, Rewrite> Rewriting;

  // selected literals
  auto itf1 = cl->getSelectedLiteralIterator();
  // rewritable subterms of selected literals
  auto itf2 = getMapAndFlattenIterator(itf1, [this](Literal *lit) -> VirtualIterator<Rewritable> {
    return pvi(pushPairIntoRightIterator(lit,
      getMappingIterator(
        EqHelper::getSubtermIterator(lit, _salg->getOrdering()),
        [](TermList term) -> Term * { return term.term(); }
      )
    ));
  });
  // all clause/literal/left-hand-sides that could rewrite the subterms of selected literals
  auto itf3 = getMapAndFlattenIterator(itf2, [this](Rewritable rewritable) -> VirtualIterator<Rewriting> {
    unsigned functor = rewritable.second->functor();
    return pvi(pushPairIntoRightIterator(rewritable,
      getMapAndFlattenIterator(
        _lhsIndex->query(functor),
        [this](Equation equation) -> VirtualIterator<Rewrite> {
          return pvi(pushPairIntoRightIterator(equation,
            EqHelper::getSuperpositionLHSIterator(
              equation.second,
              _salg->getOrdering(),
              _salg->getOptions()
            )
          ));
        }
    )));
  });
  // all successful forward superpositions on functions
  auto itf4 = getMappingIterator(itf3, [cl](Rewriting rewriting) -> Clause * {
    Rewrite rewrite = rewriting.second;
    TermList lhs = rewrite.second;
    Equation equation = rewrite.first;
    Clause *equationClause = equation.first;
    Literal *equationLiteral = equation.second;
    Clause *subtermClause = cl;
    Rewritable rewritable = rewriting.first;
    Literal *subtermLiteral = rewritable.first;
    Term *rewritten = rewritable.second;

    return superposition(
      equationClause,
      equationLiteral,
      lhs,
      subtermClause,
      subtermLiteral,
      rewritten
    );
  });

  return pvi(getFilteredIterator(itf4, [](Clause *cl) { return cl; }));
}

} //namespace Inferences
