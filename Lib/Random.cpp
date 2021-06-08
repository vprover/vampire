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
 * @file Random.cpp
 * Implements random number generation.
 *
 * @since 20/02/2000 Manchester
 * modified Ioan Dragan
 */

#include "Random.hpp"

using namespace Lib;

unsigned Random::_seed = 1;
std::mt19937 Random::_eng(Random::_seed);
