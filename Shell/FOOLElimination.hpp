
/*
 * File FOOLElimination.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

  /** Check if the unit contains expressions that are not syntactically first-order */
  static bool needsElimination(FormulaUnit* unit);

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

  // A context in one of two possible values, so we model it with bool constants
  typedef bool Context;
  static const Context TERM_CONTEXT = true;
  static const Context FORMULA_CONTEXT = false;

  // Processing of TermList and Term* returns a TermList or a Formula*,
  // depending on the context
  void process(TermList ts, Context context, TermList& termResult, Formula*& formulaResult);
  void process(Term* term,  Context context, TermList& termResult, Formula*& formulaResult);

  // Shortcuts for process(TermList)
  TermList process(TermList terms);
  Formula* processAsFormula(TermList terms);

  // Shortcuts for process(Term*)
  TermList process(Term* term);
  Formula* processAsFormula(Term* term);

  /** Processing helper functions */
  static void buildApplication(unsigned function, Formula::VarList* vars, Context context,
                               TermList& functionApplication, Formula*& predicateApplication);
  // Shortcuts for buildApplication
  static TermList buildFunctionApplication(unsigned function, Formula::VarList* vars);
  static Formula* buildPredicateApplication(unsigned predicate, Formula::VarList* vars);

  // Depending on the context, build an equivalence or an equality
  // between pairs of arguments
  static Formula* buildEq(Context context, Formula* lhsFormula, Formula* rhsFormula,
                                           TermList lhsTerm, TermList rhsTerm, unsigned termSort);

  // Creates a stack of sorts for the given variables, using the sorting
  // context of the current formula
  Stack<unsigned> collectSorts(Formula::VarList* vars);

  // Converts a boolean term t to a formula 't = true'
  static Formula* toEquality(TermList booleanTerm);

  // Introduces a fresh predicate or function (depending on the context) symbol
  // with given arguments and result sort
  static unsigned introduceFreshSymbol(Context context, const char* prefix,
                                       Stack<unsigned> sorts, unsigned resultSort);

  // In order to add some meaning to a fresh symbol we prefix it with a given string
  // Three different prefixes for three kinds of fresh symbols
  static const char* ITE_PREFIX;
  static const char* LET_PREFIX;
  static const char* BOOL_PREFIX;

  // Report that a given formula or a term has been rewritten during defooling
  // The term or formula is passed as its string representation
  static void reportProcessed(vstring inputRepr, vstring outputRepr);
};

#endif // __FOOLElimination__
