/**
 * @file Active.hpp
 * Defines the class Active of active clauses
 * @since 04/01/2008 flight Manchester-Murcia
 */

#ifndef __Active__
#define __Active__

#include "../Kernel/ClauseQueue.hpp"

using namespace Kernel;

namespace Resolution {

/**
 * Defines the class Active of active clauses
 * @since 04/01/2008 flight Manchester-Murcia
 */
class Active
  : public ClauseQueue
{
public:
  void add(Clause& c);
protected:
  virtual bool lessThan(const Clause*,const Clause*);
}; // class Active

}

#endif
