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
  void perform(int argc, char** argv);
private:

  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

  enum Color {
    ANY, LEFT, RIGHT, TRANSPARENT, NOLEFT, NORIGHT
  };

  MapToLIFO<SymId, SymId> neigh;
  DHMap<SymId, Color> symCols;

  bool tryAssignColor(SymId sym, Color c);
};


}

#endif /* __ProblemColoring__ */
