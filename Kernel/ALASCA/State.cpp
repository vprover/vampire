/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/ALASCA/State.hpp"
#include "Kernel/ALASCA/Selection.hpp"
#include "Kernel/QKbo.hpp"
#include "Kernel/ALASCA/Ordering.hpp"

namespace Kernel {

#if VDEBUG
std::shared_ptr<AlascaState> testAlascaState(Options::UnificationWithAbstraction uwa, std::shared_ptr<InequalityNormalizer> norm, Ordering* ordering, bool uwaFixedPointIteration, LiteralSelectors::SelectorMode selMode) {

  // auto qkbo = ordering == nullptr ? new QKbo(KBO::testKBO(/* rand */false, /*qkbo*/ true), norm) : nullptr;
  auto qkbo = ordering == nullptr ? new LAKBO(KBO::testKBO(/* rand */false, /*qkbo*/ true)) : nullptr;
  auto& ord = ordering == nullptr ? *qkbo : *ordering;
  return AlascaState::create(norm, &ord, uwa, uwaFixedPointIteration, AlascaSelector(&ord, selMode, /* reversePolarity */ false));
}
#endif

std::shared_ptr<AlascaState> AlascaState::globalState = nullptr;
} // namespace Kernel


