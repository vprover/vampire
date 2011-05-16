/**
 * @file Shell/Preprocess.hpp
 * Defines class Preprocess implementing problem preprocessing.
 * @since 05/01/2004 Manchester
 */

#ifndef __Preprocess__
#define __Preprocess__

#include "Kernel/Unit.hpp"

namespace Shell {

using namespace Kernel;

class Property;
class Options;

/**
 * Class implementing preprocessing-related procedures.
 * @since 16/04/2005 Manchester, made non-static
 */
class Preprocess
{
public:
  /** Initialise the preprocessor */
  explicit Preprocess(Property& property,const Options& options)
    : _property(property),
      _options(options)
  {}
  void preprocess(UnitList*& units);
private:
  Unit* preprocess1(Unit*);
  FormulaUnit* preprocess2(FormulaUnit*);
  Unit* preprocess3(Unit*);
  UnitList* normalise(UnitList*);

  /** Properties of the problem */
  Property& _property;
  /** Options used in the normalisation */
  const Options& _options;
}; // class Preprocess


}

#endif
