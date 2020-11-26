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


#include <cstdlib>
#include <ctime>

namespace Lib
{

/**
 * A fully static class for random number generation. Optimized to generate
 * random bits.
 */
class Random 
{
  /** seed */
  static int _seed;
  /** number of remaining bits */
  static int _remainingBits;
  /** number of random bits that can be extracted from one random integer */
  static const int _bitsPerInt; 
  /** integer used for extracting random bits */
  static unsigned _bits; 

  static int bitsPerInt ();     // finds _bitsPerInt;

 public:
  /* TODO:
   * https://channel9.msdn.com/Events/GoingNative/2013/rand-Considered-Harmful
   *
   * We should consider moving to c++11 approach to random number generation.
   * Although carefully, as uniform_int_distribution is implementation dependent!
   */

  /** Return the greatest random number */
  static inline int getMax () { return RAND_MAX; }

  /** Return a new random integer between 0 and RAND_MAX */
  static inline int getInteger () { return rand(); } 
  /** Return a new random integer between 0 and modulus-1 */
  static inline int getInteger (int modulus)
  { return getInteger () % modulus; }

  /** Return a new random double */
  static double getDouble(double min, double max);
  static long double getDouble(long double min , long double max);
  
  /**
   * Return a random bit. The function is optimized so it does not generates
   * a new integer upon every call.
   */
  static inline int getBit()
  {
    if ( _remainingBits == 0 ) {
      _remainingBits = _bitsPerInt;
      _bits = getInteger();
    }

    int result = _bits % 2;
    _bits /= 2;
    _remainingBits --;

    return result;
  } // Random::getBit

  // sets the random seed to s
  /** Set random seed to s */
  inline static void setSeed(int s)
  {
    _remainingBits = 0; // to "flush" the content in _bits, so that s fully determines the follow-up state

    _seed = s;
    srand(s);
  }

  /** Return the current value of the random seed. */
  inline static int seed()
  {
    return _seed;
  }

  /** Reset the seed based on the current time */
  inline static void resetSeed ()
  { setSeed(static_cast<int>(time(0))); }
}; // class Random


} // namespace Lib
#endif


