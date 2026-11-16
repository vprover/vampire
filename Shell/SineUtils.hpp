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
  void addSymIds(Term* term,DHSet<SymId, FnvHash, IdentityHash>& ids);
  void addSymIds(Literal* lit,DHSet<SymId, FnvHash, IdentityHash>& ids);
  void extractFormulaSymbols(Formula* f,DHSet<SymId, FnvHash, IdentityHash>& itms);
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
  SineSelector(float tolerance, unsigned depthLimit,
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

  /** the units below this goal affinity are subject to selection, the others are the seeds */
  GoalAffinity _threshold;
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


}

#endif /* __SineUtils__ */
