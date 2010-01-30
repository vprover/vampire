/**
 * @file SineUtils.hpp
 * Defines class SineUtils.
 */


#ifndef __SineUtils__
#define __SineUtils__

#include "../Forwards.hpp"

#include "../Lib/DArray.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Class that performs the SInE axiom selection
 */
class SineSelector
{
public:
  SineSelector();
  void perform(UnitList*& units);

private:
  typedef unsigned SymId;
  typedef VirtualIterator<SymId> SymIdIterator;

  struct FunctionSymIdFn;

  SymId getSymIdBound();
  SymId getSymId(Literal* lit, bool polarity);
  SymId getSymId(Term* t);
  void extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms);

  SymIdIterator extractSymIds(Unit* u);

  void updateDefRelation(Unit* u);

  bool _onIncluded;
  bool _strict;
  float _benevolence;

  unsigned _fnOfs;

  /** Stores symbol generality */
  DArray<unsigned> _gen;

  /** Stored the D-relation */
  DArray<UnitList*> _def;

  /**
   * Stored formulas that don't contain any symbols
   *
   * These formulas are always selected.
   */
  Stack<Unit*> _unitsWithoutSymbols;


};

}

#endif /* __SineUtils__ */
