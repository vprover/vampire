
/*
 * File Choose.hpp.
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
 * @file Choose.hpp
 * Mimics random number generation from Random with extra features.
 *
 * @since 19/08/2020 Prague
 */


#ifndef __CHOOSE__
#define __CHOOSE__

#define STR_HELPER(x) #x
#define STR(x) STR_HELPER(x)
#define HERE STR(__LINE__) "@" __FILE__

#include "Debug/Assertion.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"
#include "Lib/Int.hpp"
#include <random>
#include <fstream>
#include <string>
#include <string.h>


namespace Lib
{

/**
 * A fully static class for random number generation. Optimized to generate
 * random bits.
 */
class Choose
{
  static std::mt19937 _eng; // Standard mersenne_twister_engine

  /** the seed we got (last) seeded with */
  static unsigned _seed;

  static std::ifstream _inFile;
  static std::ofstream _outFile;

  template<typename O, typename C>
  static O read_write_generate(C callable, vstring stamp) {
    BYPASSING_ALLOCATOR;

    O res;
    vstring old_stamp;

    if (_inFile.is_open() && std::getline(_inFile,old_stamp)) {
      ASS_EQ(stamp,old_stamp);
      ALWAYS(_inFile >> res >> std::ws); // eats result and also the \n after
    } else {
      res = callable();
    }

    if (_outFile.is_open()) {
      _outFile << stamp << "\n";
      _outFile << res << endl; //flush
    }

    return res;
  }

public:

  // call at most once
  static void setInFile(const char* filename) {
    CALL("Choose::setInFile");

    BYPASSING_ALLOCATOR;

    ASS(!_inFile.is_open());
    _inFile.open(filename);
  }

  // call at most once
  static void setOutFile(const char* filename) {
    CALL("Choose::setOutFile");

    BYPASSING_ALLOCATOR;

    ASS(!_outFile.is_open());
    _outFile.open(filename);
  }

  /** Return a new random integer between 0 and modulus-1 */
  static inline int getInteger(int modulus, const char* where) {
    CALL("Choose::getInteger");

    return read_write_generate<int>([modulus]() { return std::uniform_int_distribution<int>(0,modulus-1)(_eng); },
        vstring("getInteger(") + Int::toString(modulus) + "):" + where);
  }

  /** Return a new random double */
  static double getDouble(double min, double max, const char* where) {
    CALL("Choose::getDouble");

    return read_write_generate<double>([min,max]() { return std::uniform_real_distribution<double>(min,max)(_eng); },
        vstring("getDouble(") + Int::toString(min) + ","+ Int::toString(max) + "):" + where);
  }

  /** Return a random bit. */
  static inline bool getBit(const char* where) {
    CALL("Choose::getBit");

    static std::uniform_int_distribution<int> d(0,1);

    return read_write_generate<bool>([]() { return (bool)d(_eng); },
        vstring("getBit():") + where);
  }

  // sets the random seed to s
  /** Set random seed to s */
  inline static void setSeed(unsigned s)
  {
    CALL("Choose::setSeed");

    _seed = s;
    _eng.seed(_seed);
  }

  /** Return the current value of the random seed. */
  inline static unsigned seed()
  {
    CALL("Choose::seed");

    return _seed;
  }

  /** Reset the seed based on the current time */
  inline static void resetSeed () {
    CALL("Choose::resetSeed");

    _seed = std::random_device()();
    _eng.seed(_seed);
  }

}; // class Choose


} // namespace Lib
#endif


