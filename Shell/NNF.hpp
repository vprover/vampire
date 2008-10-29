/**
 * @file NNF.hpp
 * Defines NNF-related transformations.
 * @since 28/12/2003 Manchester
 * @since 27/06/2007 Flight Frankfurt-Paris, changed to use new data structures
 */

#ifndef __NNF__
#define __NNF__

namespace Kernel {
  class Unit;
};

#include "../Kernel/Formula.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing NNF-related procedures.
 */
class NNF
{
public:
  static Unit* ennf(Unit* unit);
  static Unit* nnf(Unit* unit);
private:
  static Formula* ennf(Formula*, bool polarity);
  static FormulaList* ennf(FormulaList*, bool polarity);
  static Formula* nnf(Formula*, bool polarity);
  static FormulaList* nnf(FormulaList*, bool polarity);
}; // class NNF

}

#endif
