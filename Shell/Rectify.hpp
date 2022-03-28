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
 * @file Rectify.hpp
 * Defines class Rectify implementing the rectification inference rule.
 * @since 21/12/2003 Manchester
 */

#ifndef __Rectify__
#define __Rectify__

#include "Lib/Array.hpp"
#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/SubstHelper.hpp"

namespace Kernel {
  class Unit;
  class Clause;
  class Term;
}

using namespace Kernel;

namespace Shell {

/**
 * Class that implements rectification of formulas.
 * @since 16/01/2004 Manchester, changed to work with pre-formulas, that is,
 *   formulas in which the same variable may be both free and bound
 * @since 23/01/2004 Manchester, changed to work with non-static objects
 * 
 */
class Rectify 
{
public:
  /** Initialise Rectify */
  Rectify()
    : _free(0), _removeUnusedVars(true)
  {}
  static FormulaUnit* rectify(FormulaUnit*, bool removeUnusedVars=true);
  static void rectify(UnitList*& units);
  // for NameReuse
  Formula* rectify(Formula*);
private:
  typedef pair<unsigned,bool> VarWithUsageInfo;
  typedef List<VarWithUsageInfo> VarUsageTrackingList;
  /** Renaming stores bindings for free and bound variables */
  class Renaming
    : public Array<VarUsageTrackingList*>
  {
  public:
    Renaming()
      : Array<VarUsageTrackingList*>(15),
	_nextVar(0), _used(0)
    {
      fillInterval(0,15);
    }
    ~Renaming();
    bool tryGetBoundAndMarkUsed (int var,int& boundTo) const;
    VarWithUsageInfo getBoundAndUsage(int var) const;
    unsigned bind (unsigned v);
    void undoBinding(unsigned v);
  private:
    virtual void fillInterval (size_t start,size_t end);
    /** next variable to rename to */
    unsigned _nextVar;
    /** Variables that already appeared in the formula
     *
     * This field is used only when VarManager::varNamePreserving()
     * is true. */
    DHSet<unsigned>* _used;
  };

  void reset();

  unsigned rectifyVar(unsigned v);

  FormulaList* rectify(FormulaList*);
  void bindVars(VList*);
  void unbindVars(VList*);
  VList* rectifyBoundVars(VList*);
  TermList rectify(TermList);
  Term* rectify(Term* t);
  Term* rectifySpecialTerm(Term* t);
  Literal* rectify(Literal*);
  Literal* rectifyShared(Literal* lit);
  SList* rectifySortList(SList* from, bool& modified);
  bool rectify(TermList* from,TermList* to);

  friend class Kernel::SubstHelper;
  /** This is to allow use of SubstHelper::apply with the rectify object as applicator*/
  TermList apply(unsigned var) { return TermList(rectifyVar(var), false); }

  /** Renaming to store bindings for both free and bound variables */
  Renaming _renaming;
  /** placeholder for free variables */
  VList* _free;

  /** if true, unused quantified variables will be removed */
  bool _removeUnusedVars;

//  /** next variable to bind to */
//  int _nextVar;
//  /** next row variable to bind to */
//  int _nextRow;
}; // class Rectify

}

#endif
