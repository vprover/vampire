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

  SymIdIterator extractSymIds(Unit* u);

  void decodeSymId(SymId s, bool& pred, unsigned& functor);

private:
  struct FunctionSymIdFn;

  SymId getSymId(Literal* lit, bool polarity);
  SymId getSymId(Term* t);

  void extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms);

  unsigned _fnOfs;
};


/**
 * Class that performs the SInE axiom selection
 *
 * It has two use scenarions which must not be combined in a single
 * object:
 *
 * 1) use the @b perform(UnitList*& units) function to remove non-selected
 * units from the @b units list
 *
 * 2) first init the selection structure by @b initSelectionStructure() and
 * then select axioms for a particular problem by @b selectAxioms
 */
class SineSelector
{
public:
  SineSelector();

  void perform(UnitList*& units);

  void initSelectionStructure(UnitList* units);
  void addSelectedAxioms(UnitList*& units);
private:
  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

  void initGeneralityFunction(UnitList* units);

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
