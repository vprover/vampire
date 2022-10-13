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
  static unsigned addSkolemTypeCon(unsigned arity, unsigned var);
  static unsigned addSkolemTypeCon(unsigned arity, const char* suffix=0);  
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

  /** the collected substitution */
  Substitution _subst;

  typedef List<bool> BoolList;

  /** In the first pass (preskolemise) we collect information 
   * for each variable and in each quantified subformula
   * whether the variable appears in the subformula
   * 
   * this will get stored in _varDeps eventually,
   * but the computation uses _varOccs as a scrathpad
   * that changes through the preskolemise traversal
   * 
   * (occurs_below list in VarOccInfo below 
   *  is used to reset computation when
   *  descending below the next quantifier;
   *  thus this list works like a stack) */
  struct VarOccInfo {
    bool existential;
    BoolList* occurs_below;
  };
  // from vars to their VarOccInfo
  typedef DHMap<unsigned,VarOccInfo> VarOccInfos;
  /* starts empty at the top level, and fininshes also empty 
     after bubbling up from the recursion;
     Only used temporarily during preskolemise! */
  VarOccInfos _varOccs;

  // we are only interested in this for the existential variables
  // but still want to know both about the existential and universal occurences below "us"
  struct ExVarDepInfo {
    VarSet* univ;
    VarSet* exist;
  };
  // stored by the blocks, i.e. those Formulas* with the EXISTS connective
  typedef DHMap<Formula*,ExVarDepInfo> ExVarDepInfos; 
  ExVarDepInfos _varDeps;

  // map from an existential variable to its quantified formula (= block of quantifiers)
  DHMap<unsigned, Formula*> _blockLookup;

  /** map var --> sort */
  DHMap<unsigned,TermList> _varSorts;

  // for some heuristic evaluations after we are done
  Stack<unsigned> _introducedSkolemSyms;

  FormulaUnit* _beingSkolemised;

  // to create one big inference after we are done
  UnitList* _skolimizingDefinitions;

  bool _appify; // a higher-order solution

}; // class Skolem

}

#endif
