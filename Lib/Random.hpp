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
 * @file Random.hpp
 * Implements random number generation.
 *
 * @since 10/08/1999 Uppsala
 * @since 20/09/1999 Manchester: random bit generator added for efficiency
 * @since 18/02/2000 Manchester
 */


#ifndef __RANDOM__
#  define __RANDOM__

#include "Debug/Tracer.hpp"

#include <cstdlib>
#include <ctime>
#include <random>

namespace Lib
{

/**
 * A fully static class for random number generation. Optimized to generate
 * random bits.
 */
class Random 
{
  /* 
   * An entertaining talk on why using the c++11 approach is an improvement 
   * over the old C style via rand():
   * 
   * https://channel9.msdn.com/Events/GoingNative/2013/rand-Considered-Harmful
   *
   * Still, this is not reproducible across platforms
   * as e.g. uniform_int_distribution is implementation dependent!
   */

  static std::mt19937 _eng; // Standard mersenne_twister_engine
  /** the seed we got (last) seeded with */
  static unsigned _seed;

public:
  static inline int getInteger(int modulus) {
    CALL("Random::getInt");
    return std::uniform_int_distribution<int>(0,modulus-1)(_eng);
  }

  static double getDouble(double min, double max) {
    CALL("Random::getDouble");
    return std::uniform_real_distribution<double>(min,max)(_eng);
  }
  
  /**
   * Return a random bit.
   */
  static inline bool getBit()
  {
    return std::uniform_int_distribution<int>(0,1)(_eng);
  } // Random::getBit

  // sets the random seed to s
  /** Set random seed to s */
  inline static void setSeed(unsigned s)
  {
    CALL("Random::setSeed");

    _seed = s;
    _eng.seed(_seed);
  }

  /** Return the current value of the random seed. */
  inline static unsigned seed() { return _seed; }

  /** Try hard to set the seed to something non-deterministic random. */
  inline static void resetSeed ()
  {
    CALL("Random::resetSeed");

    setSeed(std::random_device()());
  }
}; // class Random


} // namespace Lib
#endif


