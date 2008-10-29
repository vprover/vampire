/**
 * @file Random.cpp
 * Implements random number generation.
 *
 * @since 20/02/2000 Manchester
 */

#include "Random.hpp"

using namespace Lib;

int Random::_seed = 1;
int Random::_remainingBits = 0;
const int Random::_bitsPerInt = Random::bitsPerInt ();
unsigned Random::_bits;


/**
 * An auxiliary function used to generate random bits. 
 * Returns the number of bits per integer.
 */
int Random::bitsPerInt ()
{
  int b = getMax() + 1;
  int bits = -1;

  while (b != 0) {
    b /= 2;
    bits ++;
  }

  return bits;
} // Random::bitsPerInt
