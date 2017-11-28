
/*
 * File RangeColoring.hpp.
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
  virtual ~TermColoring() {}
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

class NameMapColoring : public TermColoring
{
public:
  void loadColors(const DHMap<vstring,Color>& cols) {
    _funcColors.loadFromMap(cols);
  }
protected:
  virtual bool isColoredFunction(unsigned func);
  virtual Color getColor(TermList term);
private:
  static vstring normalizeName(vstring str);

  DHMap<vstring,Color> _funcColors;

};

}

#endif // __RangeColoring__
