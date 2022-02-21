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

  unsigned s = clause->numSelected();

  // don't shuffle between selected and non-selected literals
  shuffleArray(clause->literals(),s);
  shuffleArray(clause->literals()+s,clause->length()-s);

  // literals must be shared in typical clauses (I think), so let's not even try shuffling them

  clause->notifyLiteralReorder();
}

// iterative implementation of shuffling Formula* / Literal* / TermList
void Shuffling::shuffleIter(Shufflable sh) {
  CALL("Shuffling::shuffleIter");

  static Stack<Shufflable> todo;
  ASS(todo.isEmpty());

  todo.push(sh);

  do {
    ASS(todo.isNonEmpty());
    sh = todo.pop();

    sh_updated:

    if (sh.is<Formula*>()) {
      Formula* fla = sh.unwrap<Formula*>();

      fla_updated:

      switch (fla->connective() ) {
        case LITERAL:
        {
          sh = Shufflable(fla->literal());
          goto sh_updated;
          break; // I know, unreachable
        }
        case AND:
        case OR:
        {
          // multi-ary; shuffling subformula list
          shuffleList(*fla->argsPtr());

          // recurse to subformulas
          FormulaList::Iterator fs(fla->args());
          while (fs.hasNext()) {
            todo.push(Shufflable(fs.next()));
          }
          break;
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
          todo.push(Shufflable(fla->left()));
          fla = fla->right();
          goto fla_updated;
          break; // I know, unreachable
        }
        case NOT:
        {
          // unary; just bubble through
          fla = fla->uarg();
          goto fla_updated;
          break; // I know, unreachable
        }
        case FORALL:
        case EXISTS:
        {

          //cout << "Shuffling FORALL/EXISTS: " << fla->toString() << endl;

          // can even shuffle the variables in the quantifier!
          if (fla->sorts()) { // need to shuffle sorts in sync with vars, if they are there
            shuffleTwoList(*fla->varsPtr(),*fla->sortsPtr());
          } else {
            shuffleList(*fla->varsPtr());
          }

          //cout << "getting: " << fla->toString() << endl;

          fla = fla->qarg();

          goto fla_updated;
          break; // I know, unreachable;
        }
        case BOOL_TERM:
        {
          sh = Shufflable(fla->getBooleanTerm());
          goto sh_updated;
          break; // I know, unreachable;
        }
        case TRUE:
        case FALSE:
        {
          // bottom reached; nothing to be done
          break;
        }
        case NAME: // NamedFormula is only used by AVATAR proof documentation; so ignored here
        default:
          ASSERTION_VIOLATION;
        }
    } else if (sh.is<Literal*>()) {
      Literal* lit = sh.unwrap<Literal*>();

      if (!lit->shared()) {
        if (lit->commutative() && Random::getBit()) {
          lit->argSwap();
        }

        Term::Iterator it(lit);
        while (it.hasNext()) {
          todo.push(Shufflable(it.next()));
        }
      }
    } else {
      ASS(sh.is<TermList>());

      TermList tl = sh.unwrap<TermList>();

      tl_updated:

      if (tl.isTerm()) {
        Term* t = tl.term();
        if (!t->shared()) {
          if (t->isSpecial()) {
            Term::SpecialTermData* sd = t->getSpecialData();
            switch (sd->getType()) {
              case Term::SF_ITE:
                todo.push(Shufflable(sd->getCondition()));
                todo.push(Shufflable(*t->nthArgument(0)));
                tl = *t->nthArgument(1);
                goto tl_updated;
                break; // I know, unreachable;

              case Term::SF_FORMULA:
                todo.push(Shufflable(sd->getFormula()));
                break;

              case Term::SF_LET:
              case Term::SF_LET_TUPLE:
                todo.push(Shufflable(sd->getBinding()));
                tl = *t->nthArgument(0);
                goto tl_updated;
                break; // I know, unreachable;

              case Term::SF_TUPLE:
                tl = TermList(sd->getTupleTerm());
                goto tl_updated;
                break; // I know, unreachable;

              default:
                ASSERTION_VIOLATION_REP(tl.toString());
            }
          } else {
            Term::Iterator it(t);
            while (it.hasNext()) {
              todo.push(Shufflable(it.next()));
            }
          }
        }
      }
    }
  } while (todo.isNonEmpty());
}
