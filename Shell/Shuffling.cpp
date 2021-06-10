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
 * @file Shuffling.cpp
 * Implementing the normalisation inference rule.
 * @since 25/12/2003 Manchester
 */

#include "Lib/Sort.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"

#include "Shuffling.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Shuffle a problem
 */
void Shuffling::shuffle(Problem& prb)
{
  CALL("Shuffling::shuffle (Problem&)");

  shuffle(prb.units());
}

/**
 * Shuffle a list of units by shuffling every unit in it and
 * also shuffling the list itself.
 * @since 09/06/2021 Prague
 */
void Shuffling::shuffle (UnitList*& units)
{
  CALL("Shuffling::shuffle (UnitList*&)");

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    shuffle(us.next());
  }

  shuffleList(units);
} // Shuffling::shuffle (UnitList*)

void Shuffling::shuffle(Unit* unit)
{
  CALL("Shuffling::shuffle (Unit*");

  // cout << "Bef: " << unit->toString() << endl;

  if (unit->isClause()) {
    shuffle(unit->asClause());
  } else {
    shuffle(static_cast<FormulaUnit*>(unit)->formula());
  }

  // cout << "Aft: " << unit->toString() << endl;
}

void Shuffling::shuffle(Clause* clause)
{
  CALL("Shuffling::shuffle (Clause*)");

  shuffleArray(*clause,clause->length());

  clause->notifyLiteralReorder();
}

// TOOD: first trying to do this recursively, then turn it into the stack solution

void Shuffling::shuffle(Formula* fla)
{
  CALL("Shuffling::shuffle (Formula*)");

  switch (fla->connective() ) {
  case LITERAL:
  {
    shuffle(fla->literal());
    return;
  }
  case AND:
  case OR:
  {
    // multi-ary; shuffling subformula list
    shuffleList(*fla->argsPtr());

    // recurse to subformulas
    FormulaList::Iterator fs(fla->args());
    while (fs.hasNext()) {
      shuffle(fs.next());
    }
    return;
  }
  case IFF:
  case XOR:
  {
    // binary; can swap
    if (Random::getBit()) {
      fla->leftRightSwap();
    }
    // intentional fall-through
  case IMP:
    // binary; cannot simply swap

    // in any case, recurse to subformulas
    shuffle(fla->left());
    shuffle(fla->right());
    return;
  }
  case NOT:
  {
    // unary; just bubble through
    shuffle(fla->uarg());
    return;
  }
  case FORALL:
  case EXISTS:
  {
    // can even shuffle the variables in the quantifier!
    if (fla->sorts()) { // need to shuffle sorts in sync with vars, if they are there
      shuffleTwoList(*fla->varsPtr(),*fla->sortsPtr());
    } else {
      shuffleList(*fla->varsPtr());
    }

    shuffle(fla->qarg());
    return;
  }
  case BOOL_TERM:
  {
    // cout << "Bef: " << fla->toString() << endl;
    shuffle(fla->getBooleanTerm());
    // cout << "Aft: " << fla->toString() << endl;
    return;
  }
  case TRUE:
  case FALSE:
  {
    // bottom reached; nothing to be done
    return;
  }
  case NAME: // NamedFormula is only used by AVATAR proof documentation; so ignored here
  default:
    ASSERTION_VIOLATION;
  }
}

void Shuffling::shuffle(Literal* lit)
{
  CALL("Shuffling::shuffle (Literal*)");

  if (!lit->shared()) {
    //cout << "Bef: " << lit->toString() << endl;

    if (lit->commutative() && Random::getBit()) {
      lit->argSwap();
    }

    Term::Iterator it(lit);
    while (it.hasNext()) {
      shuffle(it.next());
    }

    //cout << "Aft: " << lit->toString() << endl;
  }
}

void Shuffling::shuffle(TermList tl)
{
  CALL("Shuffling::shuffle (TermList)");

  if (tl.isTerm()) {
    Term* t = tl.term();
    if (!t->shared()) {
      //cout << "Bef: " << t->toString() << endl;

      if (t->isSpecial()) {
        Term::SpecialTermData* sd = t->getSpecialData();
        switch (sd->getType()) {
          case Term::SF_ITE:
            shuffle(sd->getCondition());
            shuffle(*t->nthArgument(0));
            shuffle(*t->nthArgument(1));
            break;

          case Term::SF_FORMULA:
            shuffle(sd->getFormula());
            break;

          case Term::SF_LET:
          case Term::SF_LET_TUPLE:
            shuffle(sd->getBinding());
            shuffle(*t->nthArgument(0));
            break;

          case Term::SF_TUPLE:
            shuffle(TermList(sd->getTupleTerm()));
            break;

          default:
            ASSERTION_VIOLATION_REP(tl.toString());
        }
      } else {
        Term::Iterator it(t);
        while (it.hasNext()) {
          shuffle(it.next());
        }
      }

      //cout << "Aft: " << t->toString() << endl;
    }
  }
}
