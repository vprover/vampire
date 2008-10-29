/**
 * @file Unprocessed.hpp
 * Defines class Unprocessed implementing the queue of unprocessed
 * clauses.
 * @since 30/12/2007 Manchester
 */

#ifndef __Unprocessed__
#define __Unprocessed__

#include "../Kernel/ClauseQueue.hpp"

using namespace Kernel;

namespace Resolution {

/**
 * Defines Class Unprocessed implementing the queue of unprocessed clauses
 * @since 30/12/2007 Manchester
 */
class Unprocessed
  : public ClauseQueue
{
public:
  void add(Clause& c);
protected:
  virtual bool lessThan(const Clause*,const Clause*);
}; // class Unprocessed

}

#endif
