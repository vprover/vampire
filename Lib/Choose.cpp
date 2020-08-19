
/*
 * File Choose.cpp.
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
 * @file Choose.cpp
 * Mimics random number generation from Random with extra features.
 *
 * @since 19/08/2020 Prague
 */

#include "Choose.hpp"

using namespace Lib;

unsigned Choose::_seed = 1;
std::mt19937 Choose::_eng(Choose::_seed);

std::ifstream Choose::_inFile;
std::ofstream Choose::_outFile;
