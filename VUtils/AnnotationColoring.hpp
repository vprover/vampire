/**
 * @file AnnotationColoring.hpp
 * Defines class AnnotationColoring.
 */

#ifndef __AnnotationColoring__
#define __AnnotationColoring__

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

#include "Shell/SineUtils.hpp"


namespace VUtils {

using namespace Lib;
using namespace Shell;

class AnnotationColoring
{
public:
  int perform(int argc, char** argv);
private:
  typedef SineSymbolExtractor::SymId SymId;
  typedef SineSymbolExtractor::SymIdIterator SymIdIterator;
  typedef DHSet<SymId> SymIdSet;

  void outputColorInfo(ostream& out, SymId sym, string color);

  SineSymbolExtractor symEx;
  SymIdSet symbols;
  SymIdSet conjectureSymbols;
  SymIdSet axiomSymbols;

  Stack<Unit*> axiomStack;
  Stack<Unit*> conjectureStack;
};

}

#endif // __AnnotationColoring__
