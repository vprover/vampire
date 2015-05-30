/**
 * @file FOOLElimination.hpp
 * Defines class FOOLElimination.
 */

#ifndef __FOOLElimination__
#define __FOOLElimination__

#include "Forwards.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * A class with function @b apply() that eliminates all expressions
 * that are not syntactically first-order, that is:
 * - formulas in term context
 * - terms in formula context
 * - $ite-terms
 * - $let-terms
 */
class FOOLElimination {
public:
  FOOLElimination();

  void apply(Problem& prb);
  void apply(UnitList*& units);

  static bool containsFOOL(FormulaUnit* unit);

private:
  FormulaUnit* apply(FormulaUnit* fu);

  /** The currenly processed unit */
  Unit* _unit;

  /** A list of definitions, produced during preprocessing */
  UnitList* _defs;

  /** Add a new definitions to _defs */
  void addDefinition(FormulaUnit* unit);

  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;

  /** Process a given part of the unit */
  FormulaList* process(FormulaList* fs);
  Formula* process(Formula* f);
  Literal* process(Literal* literal);

  // A context in one of two possible values, so we model it with bool constants
  typedef bool context;
  static const context TERM_CONTEXT = true;
  static const context FORMULA_CONTEXT = false;

  // Processing of TermList and Term* returns a TermList or a Formula*,
  // depending on the context
  void process(TermList ts, context context, TermList& termResult, Formula*& formulaResult);
  void process(Term* term, context context, TermList& termResult, Formula*& formulaResult);

  // Shortcuts for process(TermList)
  TermList process(TermList terms);
  Formula* processAsFormula(TermList terms);

  // Shortcuts for process(Term*)
  TermList process(Term* term);
  Formula* processAsFormula(Term* term);

  /** Processing helper functions */
  static TermList buildFunctionApplication(unsigned function, Formula::VarList* vars);
  static Formula* buildPredicateApplication(unsigned predicate, Formula::VarList* vars);
  Stack<unsigned> collectSorts(Formula::VarList* vars);

  // Converts a boolean term t to a formula 't = true'
  static Formula* toEquality(TermList booleanTerm);

  /**
   * A helper class that performs replacement of all terms/literals of the form
   * f(t1, ..., tk) by g(X1, ..., Xn, t1, ..., tk) for given f, g and X1,...,Xn
   */
  // TODO: should a combination of MatcherUtils, SubstHelper be used instead?
  class SymbolOccurrenceReplacement {
    public:
      /**
       * symbol = f
       * freshSymbol = g
       * freeVars = X1, ..., Xn
       * isPredicate = whether or not f and g are predicate symbols
       */
      SymbolOccurrenceReplacement(bool isPredicate, unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars)
        : _isPredicate(isPredicate), _symbol(symbol), _freshSymbol(freshSymbol), _freeVars(freeVars) {
        // An actual replacement should take place
        ASS_NEQ(symbol, freshSymbol);
        // The implementation of this class doesn't requite freeVars to be
        // non-empty, however, its use case expects this constraint
        ASS(freeVars);
        // Arities of symbols should coincide
        if (isPredicate) {
          ASS_EQ(env.signature->getPredicate(symbol)->arity() + freeVars->length(),
                 env.signature->getPredicate(freshSymbol)->arity());
        } else {
          ASS_EQ(env.signature->getFunction(symbol)->arity() + freeVars->length(),
                 env.signature->getFunction(freshSymbol)->arity());
        }
      }
      Formula* process(Formula* formula);
      FormulaList* process(FormulaList* formulas);
      Term* process(Term* term);
      TermList process(TermList ts);

    private:
      const bool _isPredicate;
      const unsigned _symbol;
      const unsigned _freshSymbol;
      const Formula::VarList* _freeVars;
  };
};

#endif // __FOOLElimination__
