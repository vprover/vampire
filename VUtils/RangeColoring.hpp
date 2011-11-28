/**
 * @file RangeColoring.hpp
 * Defines class RangeColoring.
 */

#ifndef __RangeColoring__
#define __RangeColoring__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"

#include "Kernel/Theory.hpp"

namespace VUtils {

using namespace Lib;
using namespace Kernel;

class TermColoring {
public:
  Formula* applyToFormula(Formula* f);
  void applyToDerivation(UnitStack& inp, UnitStack& out);

  bool isLocal(Unit* u);
  bool areUnitsLocal(UnitStack& units);
protected:
  virtual bool isColoredFunction(unsigned func) = 0;
  virtual Color getColor(TermList term) = 0;

private:
  class ColoringTermTransformer;

  TermList applyToTerm(TermList trm);

  DHMap<TermList,TermList> _cache;
};

class RangeColoring : public TermColoring
{
public:
  void addFunction(unsigned func);
  void setMiddleValue(IntegerConstantType val);
protected:
  virtual bool isColoredFunction(unsigned func);
  virtual Color getColor(TermList term);
private:
  IntegerConstantType _middle;
  DHSet<unsigned> _funcs;
};

}

#endif // __RangeColoring__
