
/*
 * File ProblemColoring.hpp.
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
