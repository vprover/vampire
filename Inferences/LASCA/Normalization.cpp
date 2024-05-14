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
 * @file Normalization.cpp
 * Implements class Normalization.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/TypeList.hpp"


#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Normalization.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/LASCA.hpp"
#include "Indexing/TermIndexingStructure.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;

namespace Inferences {
namespace LASCA {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

Clause* Normalization::simplify(Clause* cl) 
{
  TIME_TRACE("perform lasca normalization")
  bool altered = false; 
  Recycled<Stack<Literal*>> out;
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lits = _shared->normalizer.normalizeLiteral((*cl)[i]);
    out->loadFromIterator(lits->iterFifo());
    altered |= lits->size() != 1 || (*lits)[0] != (*cl)[i];
  }
  if (altered) {
    Inference inf(SimplifyingInference1(Kernel::InferenceRule::LASCA_NORMALIZATION, cl));
    auto outCl = Clause::fromStack(*out, inf);
    DEBUG(*cl, " ==> ", *outCl)
    return outCl;
  } else {
    DEBUG(*cl, " stays the same")
    return cl;
  }

}

} // namespace LASCA
} // namespace Inferences
