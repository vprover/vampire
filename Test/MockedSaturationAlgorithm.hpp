/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__MOCKED_SATURATION_ALGORITHM__
#define __TEST__MOCKED_SATURATION_ALGORITHM__

#include "Saturation/Otter.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/KBO.hpp"

namespace Test {

class MockedSaturationAlgorithm : public Saturation::Otter {
public:
  MockedSaturationAlgorithm(Kernel::Problem& p, Shell::Options& o) : Otter(p,o) 
  {
  }
};

} // namespace Test

#endif // __TEST__MOCKED_SATURATION_ALGORITHM__
