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
  void addSymIds(Literal* lit, int polarity, Stack<SymId>& ids) const;

  void extractFormulaSymbols(Formula* f,int polarity,Stack<SymId>& itms);

  unsigned _fnOfs;
  unsigned _funs;
  unsigned _preds;
};


class SineBase
{
protected:
  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

  void initGeneralityFunction(UnitList* units);

  /** Stores symbol generality */
  DArray<unsigned> _gen;

  SineSymbolExtractor _symExtr;
};

/**
 * Class that performs the SInE axiom selection on a single problem
 */
class SineSelector
: public SineBase
{
public:
  SineSelector();

  void perform(UnitList*& units);
private:

  void updateDefRelation(Unit* u);

  bool _onIncluded;
  bool _strict;
  unsigned _genThreshold;
  float _tolerance;

  /** Stored the D-relation */
  DArray<UnitList*> _def;

  /**
   * Stored formulas that don't contain any symbols
   *
   * These formulas are always selected.
   */
  Stack<Unit*> _unitsWithoutSymbols;
};


/**
 * Class that can perform the SInE axiom selection for multiple problems
 * sharing the same set of theory axioms
 *
 * First init the selection structure by @b initSelectionStructure() and
 * then select axioms for a particular problem by @b addSelectedAxioms()
 */
class SineTheorySelector
: public SineBase
{
public:
  SineTheorySelector();

  void initSelectionStructure(UnitList* units);
  void addSelectedAxioms(UnitList*& units);
private:

  /** The integer tolerance value is the float option value multiplied by 10 and
   * truncated
   *
   * Therefore, if the @b maxTolerance member is equal to 50, the maximum supported
   * tolerance is 5. */
  static const unsigned short maxTolerance=50;
  static const unsigned short strictTolerance=10;

  void updateDefRelation(Unit* u);

  unsigned _genThreshold;

  struct DEntry
  {
    DEntry(unsigned short minTolerance, Unit* unit) : minTolerance(minTolerance), unit(unit) {}

    unsigned short minTolerance;
    Unit* unit;
  };
  typedef List<DEntry> DEntryList;

  /** Stored the D-relation */
  DArray<DEntryList*> _def;

  /**
   * Stored formulas that don't contain any symbols
   *
   * These formulas are always selected.
   */
  Stack<Unit*> _unitsWithoutSymbols;
};


}

#endif /* __SineUtils__ */
