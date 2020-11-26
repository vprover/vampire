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
 * @file SineUtils.hpp
 * Defines class SineUtils.
 */

#ifndef __SineUtils__
#define __SineUtils__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class SineSymbolExtractor
{
public:
  typedef unsigned SymId;
  typedef VirtualIterator<SymId> SymIdIterator;

  SymId getSymIdBound();

  SymIdIterator extractSymIds(Unit* u);

  static void decodeSymId(SymId s, bool& pred, unsigned& functor);
  bool validSymId(SymId s);
private:
  void addSymIds(Term* term,Stack<SymId>& ids);
  void addSymIds(Literal* lit,Stack<SymId>& ids);
  void extractFormulaSymbols(Formula* f,Stack<SymId>& itms);
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
  SineSelector(const Options& opt);
  SineSelector(bool onIncluded, float tolerance, unsigned depthLimit,
      unsigned genThreshold=0, bool justForSineLevels=false);

  bool perform(UnitList*& units); // returns true iff removed something
  void perform(Problem& prb);

  ~SineSelector() {
    DArray<UnitList*>::Iterator it(_def);
    while (it.hasNext()) {
      UnitList::destroy(it.next());
    }
  }
private:
  void init();

  void updateDefRelation(Unit* u);

  bool _onIncluded;
  bool _strict;
  unsigned _genThreshold;
  float _tolerance;
  unsigned _depthLimit;

  bool _justForSineLevels;

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
  SineTheorySelector(const Options& opt);

  void initSelectionStructure(UnitList* units);
  void perform(UnitList*& units);
private:

  /** The integer tolerance value is the float option value multiplied by 10 and
   * truncated
   *
   * Therefore, if the @b maxTolerance member is equal to 50, the maximum supported
   * tolerance is 5. */
  static const unsigned short maxTolerance=50;
  static const unsigned short strictTolerance=10;

  void handlePossibleSignatureChange();

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

  const Options& _opt;
};


}

#endif /* __SineUtils__ */
