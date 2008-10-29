/**
 * @file Preprocess.hpp
 * Defines class Preprocess implementing problem preprocessing.
 * @since 05/01/2004 Manchester
 */

#ifndef __Preprocess__
#define __Preprocess__

#include "../Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

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
  explicit Preprocess(const Property& property,const Options& options)
    : _property(property),
      _options(options)
  {}
  void preprocess(UnitList*& units);
private:
  Unit* preprocess1(Unit*);
  Unit* preprocess2(Unit*);
  Unit* preprocess3(Unit*);
  UnitList* normalise(UnitList*);

  /** Properties of the problem */
  const Property& _property;
  /** Options used in the normalisation */
  const Options& _options;
}; // class Preprocess


}

#endif
