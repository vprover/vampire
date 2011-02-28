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
};

class FixedRestartStrategy : public RestartStrategy {
public:
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
private:
  size_t _conflictCnt;
};

class GeometricRestartStrategy : public RestartStrategy {
public:
  /**
   * Create a geometric restart strategy with specified parameters
   *
   * The default values belong to the best-performing geometric strategy
   * in the "Jinbo Huang, The Effect of Restarts on the Efficiency of Clause
   * Learning, 2007" paper.
   */
  GeometricRestartStrategy(size_t initCnt = 32, float increase=1.1f)
  : _conflictCnt(initCnt) {}

  virtual size_t getNextConflictCount();
private:
  size_t _conflictCnt;
  float _increase;
};

}

#endif // __RestartStrategy__
