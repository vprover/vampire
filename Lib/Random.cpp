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
  //[dmitry] b should be unsigned, otherwise becomes negative
  unsigned int b = getMax() + 1;
  int bits = -1;

  while (b != 0) {
    //std::cout << "b=" << b << std::endl;
	//[dmitry] faster than division
    b >>= 1;
    bits ++;
  }

  return bits;
} // Random::bitsPerInt
