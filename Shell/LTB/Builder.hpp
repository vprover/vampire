
/*
 * File Builder.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Builder.hpp
 * Defines class Builder.
 */

#ifndef __Builder__
#define __Builder__

#include "Forwards.hpp"

#include "Shell/SineUtils.hpp"

#include "Storage.hpp"


namespace Shell
{
namespace LTB
{



class Builder {
public:
  Builder();

  void build(VirtualIterator<vstring> fnames);
private:

  /**
   * Contains maximal supported value of the tolerance parameter.
   *
   * The tolerance parameter in Options is specified as float,
   * the itolerance value is an integer value of tolerance multiplied by 100.
   */
  static const unsigned itoleranceLimit=1000;

  void updateDefRelation(Unit* u);

  /** Stores symbol generality */
  DArray<unsigned> _gen;

  typedef List<DUnitRecord> DURList;

  typedef List<DSymRecord> DSRList;

  /** Stores formulas D-related to each symbol together with tolerance level
   * that is required for their inclusion in the relation */
  DArray<DURList*> _def;

  /** Stores symbols D-related to each symbol together with tolerance level
   * that is required for their inclusion in the relation */
  DArray<DSRList*> _defSyms;

  /**
   * Stored formulas that don't contain any symbols
   *
   * These formulas are always selected.
   */
  Stack<Unit*> _unitsWithoutSymbols;

  unsigned _genThreshold;
  SineSymbolExtractor _symExtr;
};

}
}

#endif // __Builder__
