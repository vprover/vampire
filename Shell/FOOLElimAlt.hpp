/*
 * File FOOLElimAlt.hpp.
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

  /** All Du Bruijn indices in @tl greater than @cutoff are lifted by @value and new TermList returned 
    * The lift functions defined below are used during parsing and preprocessing. A non-recursive
    * lift function that assumes the absence of specials is implemented in BetaReductionEngine.hpp
    */
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
  static OperatorType* toType(unsigned sort);
  /** 
   * eta-expands function with functor @b fun and @c type
   * If @b fun is a Du Bruijn index then it is assumed that 
   * it has been pre-lifted.   
   *
   * if @b args is not null it is assumed that these arguments
   * are already eta-expanded and lifted suitably.
   */ 
  static TermList etaExpand(unsigned fun, OperatorType* type, bool ex, Stack<TermList> existingArgs);
  static TermList abstract(TermList term, unsigned termSort, Stack<unsigned> sorts);

  //During preprocessing if a formula is ever copied, its variable heads
  //require naming away from each other.
  typedef DHSet<unsigned> NatSet;
  static Formula* renameVarHeads(Formula* f, NatSet newFuncs);
  static Term* renameVarHeads(Term* term, NatSet newFuncs);
  static TermList renameVarHeads(TermList ts, NatSet newFuncs);
  static FormulaList* renameVarHeads(FormulaList* fs, NatSet newFuncs);
  static bool renameVarHeads(TermList* fromtl, TermList* totl, NatSet newFuncs);
 
  UnitList* axioms(){
	 return _axioms;
  }

private:
  typedef Signature::Symbol::HOLConstant SigSymHol;
  typedef Signature::Symbol SigSym;

  UnitList* _axioms;
  
  static unsigned addLogicalConnSym(vstring name, unsigned sort1, unsigned argNum, bool &added, SigSymHol cnst); 
  static TermList applyLogicalConn(unsigned function, TermList args1, TermList arg2, bool bothArgs = true);
  unsigned sortOf(TermList t);
  
  TermList convertToDuBruijnIndices(TermList t, Stack<int> vars);

  TermList process(TermList t);


    /** Add a new definitions to _axioms */
  void addAxiom(FormulaUnit* axiom);

  void addConnAxiom(unsigned fun, Connective conn, unsigned argSort);  



  Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  Formula* toEquality(TermList booleanTerm);
    
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;

};

#endif // __FOOLElimAlt__
