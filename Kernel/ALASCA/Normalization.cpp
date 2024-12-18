/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Normalization.hpp"

namespace Kernel {

std::shared_ptr<InequalityNormalizer> InequalityNormalizer::globalNormalizer = nullptr;

} // namespace Kernel

