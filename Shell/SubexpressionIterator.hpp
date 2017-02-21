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
       * either a term or a formula. At the same time, each object of Expression
       * has a tag with one of three values. This has to do with the way terms are
       * represented in Vampire. Objects of the class Term are non-variable terms,
       * while variables are represented as special values of TermList.
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
            TERM_LIST,
            TERM
          };

          Expression(Formula* f): Expression(f, 1) {}
          Expression(Formula* f, int polarity): _tag(FORMULA), _formula(f), _polarity(polarity) {}
          Expression(TermList ts): Expression(ts, 1) {}
          Expression(TermList ts, int polarity): _tag(TERM_LIST), _termList(ts), _polarity(polarity) {}
          Expression(Term* t): Expression(t, 1) {}
          Expression(Term* t, int polarity): _tag(TERM), _term(t), _polarity(polarity) {}

          bool isTerm() { return _tag == TERM; }
          Term* getTerm() { ASS(isTerm()); return _term; }
          bool isTermList() { return _tag == TERM_LIST; }
          TermList getTermList() { ASS(isTermList()); return _termList; }
          bool isFormula() { return _tag == FORMULA; }
          Formula* getFormula() { ASS(isFormula()); return _formula; }

          int getPolarity() { return _polarity; }

          friend class SubexpressionIterator;

        private:
          Tag _tag;
          union {
            Formula* _formula;
            TermList _termList;
            Term* _term;
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

      bool hasNext();
      Formula* next() {
        int dummy;
        return next(dummy);
      }
      Formula* next(int& polarity) {
        CALL("SubformulaIterator::next(int&)");
        ASS(hasNext());
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

      bool hasNext();
      TermList next() {
        CALL("SubtermIterator::next");
        ASS(hasNext());
        return _next;
      }

    private:
      SubexpressionIterator _sei;
      TermList _next;
  };

 }

#endif // __SubexpressionIterator__
