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
    : _free(0)
  {}
  static Unit* rectify(Unit*);
//   static void rectifyFormula(Formula&);
//   static void rectifyClause(Clause&);
private:
  typedef List<int> VarList;
  /** Renaming stores bindings for free and bound variables */
  class Renaming
    : public Array<List<int>*>
  {
  public:
    Renaming()
      : Array<List<int>*>(15),
	_nextVar(0), _used(0)
    {
      fillInterval(0,15);
    }
    ~Renaming();
    bool bound (int var,int& boundTo) const;
    int bind (int v);
    void undoBinding(int v);
  private:
    virtual void fillInterval (size_t start,size_t end);
    /** next variable to rename to */
    int _nextVar;
    /** Variables that already appeared in the formula
     *
     * This field is used only when VarManager::varNamePreserving()
     * is true. */
    DHSet<unsigned>* _used;
  };

  void reset();

  Formula* rectify(Formula*);
  FormulaList* rectify(FormulaList*);
  VarList* rectify(VarList*);
  Term* rectify(Term*);
  Literal* rectify(Literal*);
  bool rectify(TermList* from,TermList* to);
  /** Renaming to store bindings for both free and bound variables */
  Renaming _renaming;
  /** placeholder for free variables */
  List<int>* _free;
//  /** next variable to bind to */
//  int _nextVar;
//  /** next row variable to bind to */
//  int _nextRow;
}; // class Rectify

}

#endif
