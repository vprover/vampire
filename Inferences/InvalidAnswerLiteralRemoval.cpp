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
 * @file InvalidAnswerLiteralRemoval.cpp
 * Implements class InvalidAnswerLiteralRemoval.
 */

#include "InvalidAnswerLiteralRemoval.hpp"

namespace Inferences
{

Clause* InvalidAnswerLiteralRemoval::simplify(Clause* cl)
{
  // TODO: if cl contains uncomputable answer literal, return nullptr
  return cl;
}

}
