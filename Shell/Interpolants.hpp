
/*
 * File Interpolants.hpp.
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
 * @file Interpolants.hpp
 * Defines class Interpolants.
 */


#ifndef __Interpolants__
#define __Interpolants__

#include "Forwards.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Term.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Interpolants
{
public:
  Interpolants(DHSet<Unit*>* slicedOff=0) : _slicedOff(slicedOff) {}
  Formula* getInterpolant(Unit* refutation);

  static void removeConjectureNodesFromRefutation(Unit* refutation);

  static Unit* formulifyRefutation(Unit* refutation);

  // should only come after formulifyRefutation, since formulify may clear the fake colors
  static void fakeNodesFromRightButGrayInputsRefutation(Unit* refutation);

private:
  struct ItemState;

  void generateInterpolant(ItemState& st);

  UnitIterator getParents(Unit* u);

  DHSet<Unit*>* _slicedOff;

  DHMap<SplitLevel,Clause*> _splittingComponents;
};

};

#endif /* __Interpolants__ */
