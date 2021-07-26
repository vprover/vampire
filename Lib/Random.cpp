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

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Random.hpp"

using namespace Lib;

int Random::_seed = 1;
int Random::_remainingBits = 0;
const int Random::_bitsPerInt = Random::bitsPerInt ();
unsigned Random::_bits;

/**
 * Return value between @c min and @c max (excluding the bounds)
 */
double Random::getDouble (double min, double max)
{
    CALL("Random::getDouble");
    ASS_L(min, max);

    double diff = max-min;
    double part = (diff*(getInteger(RAND_MAX-2)+1))/RAND_MAX;
    return min+part;
}
long double Random::getDouble (long double min, long double max)
{
    CALL("Random::getDouble");
    ASS_L(min, max);

    long double diff = max-min;
    long double part = (diff*(getInteger(RAND_MAX-2)+1))/RAND_MAX;
    return min+part;
}

/**
 * An auxiliary function used to generate random bits. 
 * Returns the number of bits per integer.
 */
int Random::bitsPerInt ()
{
  unsigned b = (unsigned)getMax() + 1;
  int bits = -1;

  while (b != 0) {
    b /= 2;
    bits ++;
  }

  return bits;
} // Random::bitsPerInt
