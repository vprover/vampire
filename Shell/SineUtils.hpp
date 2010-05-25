/**
 * @file SineUtils.hpp
 * Defines class SineUtils.
 */


#ifndef __SineUtils__
#define __SineUtils__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class SineSymbolExtractor
{
public:
  SineSymbolExtractor();
  void onSignatureChange();

  typedef unsigned SymId;
  typedef VirtualIterator<SymId> SymIdIterator;

  SymId getSymIdBound();
  SymId getSymId(Literal* lit, bool polarity);
  SymId getSymId(Term* t);

  SymIdIterator extractSymIds(Unit* u);

private:
  struct FunctionSymIdFn;

  void extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms);

  unsigned _fnOfs;
};


/**
 * Class that performs the SInE axiom selection
 */
class SineSelector
{
public:
  SineSelector();
  void perform(UnitList*& units);

private:
  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

  void updateDefRelation(Unit* u);

  bool _onIncluded;
  bool _strict;
  unsigned _genThreshold;
  float _tolerance;

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

  SineSymbolExtractor _symExtr;
};

}

#endif /* __SineUtils__ */
