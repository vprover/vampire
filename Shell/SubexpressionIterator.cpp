/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"

#include "SubexpressionIterator.hpp"

namespace Shell {
  using namespace Lib;
  using namespace Kernel;

  SubexpressionIterator::SubexpressionIterator(Formula* f) {
    _subexpressions.push(Expression(f));
  }
  SubexpressionIterator::SubexpressionIterator(FormulaList* fs) {
    FormulaList::Iterator fi(fs);
    while (fi.hasNext()) {
      Formula* f = fi.next();
      _subexpressions.push(Expression(f));
    }
  }
  SubexpressionIterator::SubexpressionIterator(Term* t) {
    _subexpressions.push(Expression(TermList(t)));
  }
  SubexpressionIterator::SubexpressionIterator(TermList ts) {
    _subexpressions.push(Expression(ts));
  }

  bool SubexpressionIterator::hasNext() {
    CALL("SubexpressionIterator::hasNext");
    return _subexpressions.isNonEmpty();
  }

  SubexpressionIterator::Expression SubexpressionIterator::next() {
    CALL("SubexpressionIterator::next");

    ASS(hasNext());
    Expression expression = _subexpressions.pop();
    int polarity = expression._polarity;

    switch (expression._tag) {
      case Expression::Tag::FORMULA: {
        Formula* f = expression._formula;
        switch (f->connective()) {
          case LITERAL: {
            /**
             * Note that we do not propagate the polarity here, because
             * formula-level if-then-else and let-in cannot occur inside literals
             */
            Term::Iterator args(f->literal());
            while (args.hasNext()) {
              _subexpressions.push(Expression(args.next()));
            }

            break;
          }
          case AND:
          case OR: {
            FormulaList::Iterator args(f->args());
            while (args.hasNext()) {
              _subexpressions.push(Expression(args.next(), polarity));
            }
            break;
          }

          case IMP:
            _subexpressions.push(Expression(f->left(), -polarity));
            _subexpressions.push(Expression(f->right(), polarity));
            break;

          case IFF:
          case XOR:
            _subexpressions.push(Expression(f->left(),  0));
            _subexpressions.push(Expression(f->right(), 0));
            break;

          case NOT:
            _subexpressions.push(Expression(f->uarg(), -polarity));
            break;

          case FORALL:
          case EXISTS:
            _subexpressions.push(Expression(f->qarg(), polarity));
            break;

          case BOOL_TERM:
            /**
             * Note, that here we propagate the polarity from the formula to
             * its underlying boolean term. This is the only place in the code
             * where the polarity of a term can be set to negative.
             */
            _subexpressions.push(Expression(f->getBooleanTerm(), polarity));
            break;

          default:
            break;
        }
        break;
      }

      case Expression::Tag::TERM: {
        TermList ts = expression._term;

        if (ts.isVar()) {
          break;
        }

        ASS(ts.isTerm());
        Term* term = ts.term();

        if (term->isSpecial()) {
          Term::SpecialTermData* sd = term->getSpecialData();
          switch (sd->getType()) {
            case Term::SF_FORMULA:
              /**
               * Note that here we propagate the polarity of the boolean term to its
               * underlying formula
               */
              _subexpressions.push(Expression(sd->getFormula(), polarity));
              break;

            case Term::SF_ITE: 
              /**
               * Regardless of the polarity of the whole if-then-else expression,
               * the polarity of the condition is always 0. This is because you
               * can always see "$ite(C, A, B)" as "(C => A) && (~C => B)"
               */
              _subexpressions.push(Expression(sd->getCondition(), 0));
              _subexpressions.push(Expression(*term->nthArgument(0), polarity));
              _subexpressions.push(Expression(*term->nthArgument(1), polarity));
              break;

            case Term::SF_LET:
            case Term::SF_LET_TUPLE: 
              /**
               * The polarity of the body of let-bindings is 0.
               * An expression "$let(f := A, ...)", where A is a formula,
               * is semantically equivalent to f <=> A && ...
               */
              _subexpressions.push(Expression(sd->getBinding(), 0));
              _subexpressions.push(Expression(*term->nthArgument(0), polarity));
              break;

            case Term::SF_LAMBDA:
			       _subexpressions.push(Expression(sd->getLambdaExp(), polarity));
			       break;

            /*case Term::SF_TUPLE:
              _subexpressions.push(Expression(sd->getTupleTerm()));
              break; */

            case Term::SF_MATCH: {
              for (unsigned i = 0; i < term->arity(); i++) {
                _subexpressions.push(Expression(*term->nthArgument(i), polarity));
              }
              break;
            }

#if VDEBUG
            default:
              ASSERTION_VIOLATION_REP(term->toString());
#endif
          }
        } else {
          Term::Iterator args(term);
          while (args.hasNext()) {
            _subexpressions.push(Expression(args.next()));
          }
        }
        break;
      }

#if VDEBUG
      default:
        ASSERTION_VIOLATION_REP(expression._tag);
#endif
    }

    return expression;
  }
}
