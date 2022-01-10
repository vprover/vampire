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
 * An iterator over all subexpressions (subterms and subformulas) of a given
 * expression. This iterator is aware of FOOL, that is, boolean terms might
 * occur as formulas, and formulas might occur as arguments.
 *
 * Iterators over subformulas and subterms (defined below) are trivial special
 * cases of this iterator
 */

#ifndef __SubexpressionIterator__
#define __SubexpressionIterator__

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Shell {
  using namespace Lib;
  using namespace Kernel;

  // FoolAwareSubexpressionIterator
  class SubexpressionIterator { //: public IteratorCore<SubexpressionIterator::Expression> {
    public:
      CLASS_NAME(SubexpressionIterator);
      USE_ALLOCATOR(SubexpressionIterator);
      /**
       * SubexpressionIterator::Expression represents an expression, which is
       * either a term or a formula. Terms are stored as objects of TermList,
       * and not of Term. This has to do with the way Vampire represents terms.
       * Objects of the class Term are non-variable terms, while variables are
       * represented as special values of TermList.
       *
       * Each expression has a polarity. For formula expressions, this is the
       * polarity of the formula. For terms, polarity is not meaningful, but it
       * is necessary for formula-level if-then-else and let-in.
       *
       * Consider the expression "~$ite(A, B, C)", where A, B and C are formulas.
       * If-then-else expressions are stored as terms, with both branches stored as
       * terms as well. The representation of this expression in Vampire is
       * "~$term{$ite(A, $formula{B}, $formula{C})}".
       * If the polarity of the whole expression is positive, the polarities of A
       * and B must be negative because of the negation. To handle that correctly,
       * we first propagate the negative polarity from the formula to its underlying
       * boolean term, and then from the boolean terms to their underlying formulas.
       *
       * NOTE: this iterator returns sort terms as well. As of 25/11/2021, the only 
       * use of this iterator is in Property.cpp.
       */
      class Expression {
        public:
          enum Tag {
            FORMULA,
            TERM
          };

          Expression(Formula* f): Expression(f, 1) {}
          Expression(Formula* f, int polarity): _tag(FORMULA), _formula(f), _polarity(polarity) {}
          Expression(TermList ts): Expression(ts, 1) {}
          Expression(TermList ts, int polarity): _tag(TERM), _term(ts), _polarity(polarity) {}
          Expression(Term* t): Expression(TermList(t)) {}
          Expression(Term* t, int polarity): Expression(TermList(t), polarity) {}

          bool isTerm() { return _tag == TERM; }
          TermList getTerm() { ASS(isTerm()); return _term; }

          bool isFormula() { return _tag == FORMULA; }
          Formula* getFormula() { ASS(isFormula()); return _formula; }

          int getPolarity() { return _polarity; }

          friend class SubexpressionIterator;

        private:
          Tag _tag;
          union {
            Formula* _formula;
            TermList _term;
          };
          int _polarity;
      };

      bool hasNext();
      Expression next();

      SubexpressionIterator(Formula* f);
      SubexpressionIterator(FormulaList* fs);
      SubexpressionIterator(Term* t);
      SubexpressionIterator(TermList ts);

    private:
      Stack<Expression> _subexpressions;
  };

  class FoolAwareSubformulaIterator : public IteratorCore<Formula*> {
    public:
      FoolAwareSubformulaIterator(Formula* f): _sei(f) {}
      FoolAwareSubformulaIterator(FormulaList* fs): _sei(fs) {}
      FoolAwareSubformulaIterator(Term* t): _sei(t) {}
      FoolAwareSubformulaIterator(TermList ts): _sei(ts) {}

      bool hasNext() {
        CALL("FoolAwareSubformulaIterator::hasNext");
        while (_sei.hasNext()) {
          SubexpressionIterator::Expression expression = _sei.next();
          if (expression.isFormula()) {
            _next = expression.getFormula();
            _polarity = expression.getPolarity();
            return true;
          }
        }
        return false;
      }
      Formula* next() {
        int dummy;
        return next(dummy);
      }
      Formula* next(int& polarity) {
        CALL("FoolAwareSubformulaIterator::next(int&)");
        ASS(_next);
        polarity = _polarity;
        return _next;
      }

    private:
      SubexpressionIterator _sei;
      Formula* _next;
      int _polarity;
  };

  class FoolAwareSubtermIterator : public IteratorCore<TermList> {
    public:
      FoolAwareSubtermIterator(Formula* f): _sei(f) {}
      FoolAwareSubtermIterator(FormulaList* fs): _sei(fs) {}
      FoolAwareSubtermIterator(Term* t): _sei(t) {}
      FoolAwareSubtermIterator(TermList ts): _sei(ts) {}

      bool hasNext() {
        CALL("FoolAwareSubtermIterator::hasNext");
        while (_sei.hasNext()) {
          SubexpressionIterator::Expression expression = _sei.next();
          if (expression.isTerm()) {
            _next = expression.getTerm();
            return true;
          }
        }
        return false;
      }
      TermList next() {
        return _next;
      }

    private:
      SubexpressionIterator _sei;
      TermList _next;
  };
}

#endif // __SubexpressionIterator__
