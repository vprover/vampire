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

  void build(VirtualIterator<string> fnames);
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
