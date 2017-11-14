
/*
 * File Skolem.hpp.
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
 * @file Skolem.hpp
 * Defines class Skolem implementing skolemisation.
 * @since 05/01/2004 Manchester
 * @since 08/07/2007 Manchester Airport, changed to new datastructures
 */

#ifndef __Skolem__
#define __Skolem__

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Substitution.hpp"

namespace Kernel {
  class Unit;
}

using namespace Lib;
using namespace Kernel;

namespace Shell {

// class Formula;
// class FormulaList;

/**
 * Class implementing skolemisation-related procedures.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 */
class Skolem
{
public:
  static FormulaUnit* skolemise(FormulaUnit*);
  static unsigned addSkolemFunction(unsigned arity, unsigned* domainSorts,
      unsigned rangeSort, unsigned var);
  static unsigned addSkolemFunction(unsigned arity, unsigned* domainSorts,
      unsigned rangeSort, const char* suffix=0);
  static unsigned addSkolemPredicate(unsigned arity, unsigned* domainSorts, unsigned var);
  static unsigned addSkolemPredicate(unsigned arity, unsigned* domainSorts, const char* suffix=0);
private:
  /** Initialise a Skolem object */
  Skolem () :  _beingSkolemised(0) {}
  FormulaUnit* skolemiseImpl(FormulaUnit*);

  // create substitution, based on occurrences
  void preskolemise(Formula*);
  // drop existential quantifiers and apply substitution
  Formula* skolemise(Formula*);
  FormulaList* skolemise(FormulaList*);

  void ensureHavingVarSorts();

  /** collected substitution */
  Substitution _subst;

  typedef List<bool> BoolList;

  /** In the first pass we collect information about
   * whether a variable appears in a subformula
   * (occurs_below list is used to reset computation when
   * descending below the next quantifier;
   * thus this list works like a stack) */
  struct VarOccInfo {
    bool existential;
    BoolList* occurs_below;
  };
  typedef DHMap<unsigned,VarOccInfo> VarOccInfos;
  VarOccInfos _varOccs;

  struct ExVarDepInfo {
    VarSet* univ;
    VarSet* exist;
  };

  typedef DHMap<Formula*,ExVarDepInfo> ExVarDepInfos; // stored by the blocks
  ExVarDepInfos _varDeps;

  // map from an existential variable to its quantified formula (= block of quantifiers)
  DHMap<unsigned, Formula*> _blockLookup;

  /** map var --> sort */
  DHMap<unsigned,unsigned> _varSorts;

  Stack<unsigned> _introducedSkolemFuns;

  FormulaUnit* _beingSkolemised;

  UnitList* _skolimizingDefinitions;

}; // class Skolem

}

#endif
