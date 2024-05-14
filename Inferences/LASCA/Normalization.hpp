/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Normalization.hpp
 * Defines class Normalization
 *
 */

#ifndef __LASCA_Normalization__
#define __LASCA_Normalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Kernel/LASCA.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Normalization
: public ImmediateSimplificationEngine 
{
  std::shared_ptr<LascaState> _shared;
public: 
  Normalization(std::shared_ptr<LascaState> shared) : _shared(std::move(shared)) {}
  USE_ALLOCATOR(Normalization);

  virtual Clause* simplify(Clause* cl) final override;
};

} // namespace LASCA
} // namespace Inferences

#endif /*__LASCA_Normalization__*/
