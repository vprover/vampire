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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"

#include "Inferences/InductionHelper.hpp"

#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/TermSubstitutionTree.hpp"

#include "TermIndex.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionSubtermIndex::handleClause");

  TIME_TRACE("backward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    VirtualIterator<Term*> rsti;
#if VHOL    
    if(!env.property->higherOrder()){
#endif
      rsti = EqHelper::getSubtermIterator(lit,_ord);
#if VHOL    
    } else {
      rsti = EqHelper::getFoSubtermIterator(lit,_ord);
    }
#endif

    while (rsti.hasNext()) {
      auto tt = TypedTermList(rsti.next());
      ((TermSubstitutionTree*)&*_is)->handle(tt, lit, c, adding);
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionLHSIndex::handleClause");

  TIME_TRACE("forward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
	    _tree->handle(TypedTermList(lhsi.next(), SortHelper::getEqualityArgumentSort(lit)), lit, c, adding);
    }
  }
}

template <class SubtermIterator>
void DemodulationSubtermIndex<SubtermIterator>::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationSubtermIndex::handleClause");

  TIME_TRACE("backward demodulation index maintenance");

  static DHSet<Term*> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    // it is true (as stated below) that inserting only once per clause would be sufficient
    // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
    // so if the order changes while a clause is in the index (which can happen with "-sa otter")
    // the removes could be called on different literals than the inserts!
    inserted.reset();
    Literal* lit=(*c)[i];
    SubtermIterator it(lit);
    while (it.hasNext()) {
      Term* t= it.next();
      if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        it.right();
        continue;
      }
      if (adding) {
        _is->insert(TypedTermList(t), lit, c);
      }
      else {
        _is->remove(TypedTermList(t), lit, c);
      }
    }
  }
}

#if VHOL
template class DemodulationSubtermIndex<DemodulationSubtermIt>;
#endif
template class DemodulationSubtermIndex<NonVariableNonTypeIterator>;

void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationLHSIndex::handleClause");

  if (c->length()!=1) {
    return;
  }

  TIME_TRACE("forward demodulation index maintenance");

  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt);
  while (lhsi.hasNext()) {
    auto lhs = lhsi.next();
    TypedTermList tt(lhs, SortHelper::getTermSort(lhs, lit));
    if (adding) {
      _is->insert(tt, lit, c);
    }
    else {
      _is->remove(tt, lit, c);
    }
  }
}

void InductionTermIndex::handleClause(Clause* c, bool adding)
{
  CALL("InductionTermIndex::handleClause");

  TIME_TRACE("induction term index maintenance");

  if (InductionHelper::isInductionClause(c)) {
  // Iterate through literals & check if the literal is suitable for induction
    for (unsigned i=0;i<c->length();i++) {
      Literal* lit = (*c)[i];
      if (InductionHelper::isInductionLiteral(lit)) {
        SubtermIterator it(lit);
        while (it.hasNext()) {
          TermList tl = it.next();
          if (!tl.term()) continue;
          // TODO: each term (and its subterms) should be processed
          // only once per literal, see DemodulationSubtermIndex
          Term* t = tl.term();
          if (InductionHelper::isInductionTermFunctor(t->functor()) &&
              InductionHelper::isIntInductionTermListInLiteral(t, lit)) {
            if (adding) {
              _is->insert(TypedTermList(t), lit, c);
            } else {
              _is->remove(TypedTermList(t), lit, c);
            }
          }
        }
      }
    }
  }
}

void StructInductionTermIndex::handleClause(Clause* c, bool adding)
{
  CALL("StructInductionTermIndex::handleClause");

  if (!InductionHelper::isInductionClause(c)) {
    return;
  }
  static DHSet<TermList> inserted;
  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    inserted.reset();
    Literal* lit = (*c)[i];
    if (!lit->ground()) {
      continue;
    }
    SubtermIterator it(lit);
    while (it.hasNext()) {
      TermList tl = it.next();
      if (!inserted.insert(tl)) {
        it.right();
        continue;
      }
      ASS(tl.isTerm());
      Term* t = tl.term();
      if (InductionHelper::isInductionTermFunctor(t->functor()) &&
          InductionHelper::isStructInductionFunctor(t->functor())) {
        if (adding) {
          _is->insert(TypedTermList(t), lit, c);
        } else {
          _is->remove(TypedTermList(t), lit, c);
        }
      }
    }
  }
}


/////////////////////////////////////////////////////
// Indices for higher-order inferences from here on//
/////////////////////////////////////////////////////

#if VHOL

void SkolemisingFormulaIndex::insertFormula(TermList formula, TermList skolem)
{
  CALL("SkolemisingFormulaIndex::insertFormula");
  _is->insert(TypedTermList(formula.term()), skolem);
}

#endif

} // namespace Indexing
