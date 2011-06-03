/**
 * @file InterpolantMinimizer.hpp
 * Defines class InterpolantMinimizer.
 */

#ifndef __InterpolantMinimizer__
#define __InterpolantMinimizer__

#include "Lib/DHSet.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/InferenceStore.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class InterpolantMinimizer {
public:
  typedef InferenceStore::UnitSpec UnitSpec;


private:

  void traverse(Clause* refutation);

  struct TraverseStackEntry;

  enum UnitState {
    TRANSPARENT_ANCESTORS,
    HAS_LEFT_PARENT,
    HAS_RIGHT_PARENT
  };

  struct UnitInfo
  {
    UnitInfo() : state(TRANSPARENT_ANCESTORS), isRefutation(false),
	isParentOfLeft(false), isParentOfRight(false), leadsToColor(false) {}

    Color color;

    UnitState state;

    bool isRefutation;
    bool isParentOfLeft;
    bool isParentOfRight;

    /** True if unit has some non-transparent ancestor (doesn't need to be immediate) */
    bool leadsToColor;
  };

  Unit* _refutation;

  /** Either the refutation, or transparent units used as premise for a non */
  Stack<Unit*> redSeeds;

  MapToLIFO<UnitSpec,UnitSpec> _parents;
  DHMap<UnitSpec,UnitInfo> _infos;
};

}

#endif // __InterpolantMinimizer__
