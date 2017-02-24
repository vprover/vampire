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

  class SubexpressionIterator { //: public IteratorCore<SubexpressionIterator::Expression*> {
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
       */
      class Expression {
        public:
          CLASS_NAME(SubexpressionIterator::Expression);
          USE_ALLOCATOR(SubexpressionIterator::Expression);

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
      Expression* next();

      SubexpressionIterator(Formula* f);
      SubexpressionIterator(FormulaList* fs);
      SubexpressionIterator(Term* t);
      SubexpressionIterator(TermList ts);

    private:
      Stack<Expression*> _subexpressions;
  };

  class SubformulaIterator : public IteratorCore<Formula*> {
    public:
      SubformulaIterator(Formula* f): _sei(f) {}
      SubformulaIterator(FormulaList* fs): _sei(fs) {}
      SubformulaIterator(Term* t): _sei(t) {}
      SubformulaIterator(TermList ts): _sei(ts) {}

      bool hasNext() {
        CALL("SubformulaIterator::hasNext");
        while (_sei.hasNext()) {
          SubexpressionIterator::Expression* expression = _sei.next();
          if (expression->isFormula()) {
            _next = expression->getFormula();
            _polarity = expression->getPolarity();
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
        CALL("SubformulaIterator::next(int&)");
        ASS(_next);
        polarity = _polarity;
        return _next;
      }

    private:
      SubexpressionIterator _sei;
      Formula* _next;
      int _polarity;
  };

  class SubtermIterator : public IteratorCore<TermList> {
    public:
      SubtermIterator(Formula* f): _sei(f) {}
      SubtermIterator(FormulaList* fs): _sei(fs) {}
      SubtermIterator(Term* t): _sei(t) {}
      SubtermIterator(TermList ts): _sei(ts) {}

      bool hasNext() {
        CALL("SubtermIterator::hasNext");
        while (_sei.hasNext()) {
          SubexpressionIterator::Expression* expression = _sei.next();
          if (expression->isTerm()) {
            _next = expression->getTerm();
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
