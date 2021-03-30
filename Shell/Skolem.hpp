/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
  static FormulaUnit* skolemise(FormulaUnit*, bool appify = false);
  static unsigned addSkolemFunction(unsigned arity, TermList* domainSorts, TermList rangeSort, unsigned var, unsigned taArity = 0);
  static unsigned addSkolemFunction(unsigned arity, unsigned taArity, TermList* domainSorts, TermList rangeSort, const char* suffix=0);
  static unsigned addSkolemPredicate(unsigned arity, TermList* domainSorts, unsigned var, unsigned taArity = 0);
  static unsigned addSkolemPredicate(unsigned arity, unsigned taArity, TermList* domainSorts, const char* suffix=0);
private:
  /** Initialise a Skolem object */
  Skolem () :  _beingSkolemised(0) {}
  FormulaUnit* skolemiseImpl(FormulaUnit*, bool appify);

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
  DHMap<unsigned,TermList> _varSorts;

  Stack<unsigned> _introducedSkolemFuns;

  FormulaUnit* _beingSkolemised;

  UnitList* _skolimizingDefinitions;

  bool _appify; // a higher-order solution

}; // class Skolem

}

#endif
