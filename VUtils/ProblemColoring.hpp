/*
 * ProblemColoring.hpp
 */

#ifndef __ProblemColoring__
#define __ProblemColoring__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/MapToLIFO.hpp"

#include "Shell/SineUtils.hpp"

namespace  VUtils {

using namespace Shell;

class ProblemColoring
{
public:
  int perform(int argc, char** argv);
private:

  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

  enum Color {
    ANY, LEFT, RIGHT, TRANSPARENT, NOLEFT, NORIGHT
  };
  struct SymIdComparator;

  SineSymbolExtractor symEx;
  MapToLIFO<SymId, SymId> neigh;
  DHMap<SymId, Color> symCols;

  bool tryAssignColor(SymId sym, Color c);
  Color getUnitColor(Unit* u);
};


}

#endif /* __ProblemColoring__ */
