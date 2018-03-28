/**
 * @file FOOLElimAlt.hpp
 * Defines class FOOLElimAlt.
 */

#ifndef __FOOLElimAlt__
#define __FOOLElimAlt__

#include "Forwards.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * FOOLElimination.cpp translates formulas in term contexts by renaming them.
 * This does not work if the formulas contain Du Bruijn indices as these
 * indices can then incorrectly become free. This class defines an alternative 
 * translation for formulas in term context.
 */
class FOOLElimAlt {
public:

  FOOLElimAlt(DHMap<unsigned,unsigned> varSorts) : _axioms(0), _varSorts(varSorts){};
  static unsigned addDuBruijnIndex(vstring name, OperatorType* type);
  TermList formulaToTerm(Formula* fm);  

  //All functions below are here temporarily until a more suitable class is created for them, AYB!
  /** All Du Bruijn indices in @tl greater than @cutoff are lifted by @value and new TermList returned */
  static TermList lift(TermList tl, unsigned value, unsigned cutoff);
  static bool lift(TermList* fromtl, TermList* totl, unsigned value, unsigned cutoff);
  static Term* lift(Term* term, unsigned value, unsigned cutoff);
  static Formula* lift(Formula* formula, unsigned value, unsigned cutoff);
  static FormulaList* lift(FormulaList* fs, unsigned value, unsigned cutoff);
  /**if @name represents Du Bruijn Index, lifts it by @value */
  static vstring lift(vstring name, unsigned value);
  /** returns true iff @index represents an index of value greater than @cutoff */
  static bool indexGreater(vstring index, unsigned cutoff);
  static unsigned toSort(OperatorType* type);
  
  UnitList* axioms(){
	 return _axioms;
  }

private:
  UnitList* _axioms;
  
  static unsigned addLogicalConnSym(vstring name, unsigned sort1, unsigned argNum, bool &added); 
  static TermList applyLogicalConn(unsigned function, TermList args1, TermList arg2, bool bothArgs = true);

  TermList convertToDuBruijnIndices(TermList t, Stack<int> vars);
  TermList abstract(TermList term, Stack<unsigned> sorts);
  TermList process(TermList t);
  unsigned sortOf(TermList t);

    /** Add a new definitions to _axioms */
  void addAxiom(FormulaUnit* axiom);

  void addConnAxiom(unsigned fun, Connective conn, unsigned argSort);  



  Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  Formula* toEquality(TermList booleanTerm);
    
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;

};

#endif // __FOOLElimAlt__
