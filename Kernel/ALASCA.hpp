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
 * @file ALASCA.cpp
 * Defines all functionality shared among the components of the inequality resolution calculus.
 *
 */

#ifndef __ALASCA__
#define __ALASCA__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/STL.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/ALASCA/Signature.hpp"

#undef DEBUG
#endif // __ALASCA__

