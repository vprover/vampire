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
 
  TermList formulaToTerm(Formula* fm);  
  static unsigned addLogicalConnSym(vstring name, unsigned sort1, unsigned argNum, bool &added); 
  static TermList applyLogicalConn(unsigned function, TermList args1, TermList arg2, bool bothArgs = true);
  
  UnitList* axioms(){
	 return _axioms;
  }

private:
  UnitList* _axioms;
  
  TermList abstract(TermList term, Stack<unsigned> sorts);
  TermList process(TermList t);
  unsigned sortOf(TermList t);

    /** Add a new definitions to _axioms */
  void addAxiom(FormulaUnit* axiom);

  void addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned qvarSort);
  void addConnAxiom(unsigned fun, Connective conn, unsigned argSort);  

  unsigned range(unsigned sort);
  unsigned domain(unsigned sort);
  
  Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  Formula* toEquality(TermList booleanTerm);
  
  TermList addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant constant);
  
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;

};

#endif // __FOOLElimAlt__
