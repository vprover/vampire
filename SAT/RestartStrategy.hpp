
/*
 * File RestartStrategy.hpp.
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
 * @file RestartStrategy.hpp
 * Defines class RestartStrategy.
 */

#ifndef __RestartStrategy__
#define __RestartStrategy__

#include "Forwards.hpp"

namespace SAT {

class RestartStrategy {
public:
  virtual ~RestartStrategy() {}

  virtual size_t getNextConflictCount() = 0;
  virtual void reset() = 0;

protected:
  static size_t increase(size_t val, float quotient);
};

class FixedRestartStrategy : public RestartStrategy {
public:
  CLASS_NAME(FixedRestartStrategy);
  USE_ALLOCATOR(FixedRestartStrategy);

  /**
   * Create restart strategy with specified number of conflicts between
   * restarts
   *
   * The default value 16,000 belong to the best-performing fixed strategy
   * in the "Jinbo Huang, The Effect of Restarts on the Efficiency of Clause
   * Learning, 2007" paper.
   */
  FixedRestartStrategy(size_t conflictCnt = 16000)
  : _conflictCnt(conflictCnt) {}

  virtual size_t getNextConflictCount() { return _conflictCnt; }
  virtual void reset() {}
private:
  size_t _conflictCnt;
};

class GeometricRestartStrategy : public RestartStrategy {
public:
  CLASS_NAME(GeometricRestartStrategy);
  USE_ALLOCATOR(GeometricRestartStrategy);

  /**
   * Create a geometric restart strategy with specified parameters
   *
   * The default values belong to the best-performing geometric strategy
   * in the "Jinbo Huang, The Effect of Restarts on the Efficiency of Clause
   * Learning, 2007" paper.
   */
  GeometricRestartStrategy(size_t initCnt = 32, float increase=1.1f)
  : _initConflictCnt(initCnt), _conflictCnt(initCnt), _increase(increase) {}

  virtual size_t getNextConflictCount();
  virtual void reset() { _conflictCnt = _initConflictCnt; }
private:
  size_t _initConflictCnt;
  size_t _conflictCnt;
  float _increase;
};

class LubyRestartStrategy : public RestartStrategy {
public:
  CLASS_NAME(LubyRestartStrategy);
  USE_ALLOCATOR(LubyRestartStrategy);

  /**
   * Create a Luby restart strategy with specified factor
   *
   * The algorithm from Luby numbers and the factor default value is based on
   * http://www.satcompetition.org/gorydetails/?p=3
   */
  LubyRestartStrategy(size_t factor = 512)
  : _index(1), _factor(factor) {}

  virtual size_t getNextConflictCount() { return getLubyNumber(_index++)*_factor; }
  virtual void reset() { _index = 1; }
private:
  static size_t getLubyNumber(size_t i);

  size_t _index;
  size_t _factor;
};

class MinisatRestartStrategy : public RestartStrategy {
public:
  CLASS_NAME(MinisatRestartStrategy);
  USE_ALLOCATOR(MinisatRestartStrategy);

  /**
   * Create a Minisat restart strategy with specified parameters
   *
   * According to "Armin Biere, PicoSAT Essentials" paper.
   */
  MinisatRestartStrategy(size_t initCnt = 100, float increase=1.1f)
  : _initConflictCnt(initCnt), _increase(increase) { reset(); }

  virtual size_t getNextConflictCount();
  virtual void reset() { _innerCnt = _outerCnt = _initConflictCnt; }
private:
  size_t _initConflictCnt;
  size_t _innerCnt;
  size_t _outerCnt;
  float _increase;
};

}

#endif // __RestartStrategy__
