/**
 * @file EPRSkolem.hpp
 * Defines class EPRSkolem.
 */

#ifndef __EPRSkolem__
#define __EPRSkolem__

#include "Forwards.hpp"

#include "EPRInlining.hpp"

namespace Shell {

/**
 * Perform EPR preserving skolemization of definitions
 *
 * One may either use the apply(UnitList*&) function to skolemize the
 * whole problem, or it can be done formula by formula using:
 *
 * FormulaUnit* constantSkolemize(FormulaUnit* unit)
 * to skolemize existential quantifier that can be replaced by constants
 *
 * PDInliner class to inline predicate equivalences
 *
 * scan(UnitList*) to detect definitions
 *
 * bool apply(Unit* unit, UnitList*& res) to replace definitions by their
 * skolemized form
 */
class EPRSkolem : public EPRRestoring {
public:
  EPRSkolem() : EPRRestoring()/*, _defs(0) MS: unused*/ {}

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(Unit* unit, UnitList*& res);

  static FormulaUnit* constantSkolemize(FormulaUnit* unit);
protected:
  virtual void processActiveDefinitions(UnitList* units);
private:
  void enableLiteralHeader(unsigned header);
  void processLiteralHeader(Literal* lit, unsigned header);
  void processProblemLiteral(Literal* lit, int polarity);
  void processProblemClause(Clause* cl);
  void processProblemFormula(FormulaUnit* fu);

  bool applyToDefinitionHalf(FormulaUnit* fu, Literal* lhs, Formula* rhs,
      int topPolarity, UnitList*& res);
  void processDefinition(FormulaUnit* unit);

  FormulaUnit* definitionToImplication(FormulaUnit* premise, Literal* lhs,
      Formula* rhs, int topPolarity);

  static vstring headerToString(unsigned hdr);

  class Applicator;
  class ConstantSkolemizer;
  class CannotEPRSkolemize : public Exception {};


  typedef MapToLIFO<unsigned,Literal*> InstMap;

  /**
   * Map from literal headers that should have EPR violating
   * definition inlined, to the list of their instances among
   * formulas which aren't active definitions.
   */
  InstMap _insts;

  DHSet<unsigned> _inlinedHeaders;

  /** Set of (EPR inlineable) literal headers that have non-ground
   * instances among formulas which aren't active definitions. */
  DHSet<unsigned> _haveNonground;

  typedef DHMap<Unit*,UnitList*> ReplacementMap;

  /** Map from definitions to their replacements */
  ReplacementMap _replacements;

  // UnitList* _defs; // MS: unused
};

}

#endif // __EPRSkolem__
