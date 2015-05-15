/**
 * @file FOOLElimination.hpp
 * Defines class FOOLElimination.
 */

#ifndef __FOOLElimination__
#define __FOOLElimination__

#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

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
  TermList process(TermList ts);
  TermList process(Term* t);

  /** Processing helper functions */
  TermList buildFunctionApplication(unsigned function, Formula::VarList* vars);
  Literal* buildPredicateApplication(unsigned predicate, Formula::VarList* vars);
  Stack<unsigned> collectSorts(Formula::VarList* vars);

  /** Replace an occurrence of a symbol with freshSymbol, appending freeVars as additional arguments */
  // TODO: should a combination of MatcherUtils, SubstHelper be used instead?
  FormulaList* replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, FormulaList* formulas);
  Formula* replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, Formula* formula);
  TermList replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, TermList ts);
  Term* replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, Term* term);
};

}

#endif // __FOOLElimination__
