/**
 * @file ClauseSharing.hpp
 * Defines class ClauseSharing.
 */


#ifndef __ClauseSharing__
#define __ClauseSharing__

#include "../Debug/Assertion.hpp"

#include "../Lib/Set.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "SATClause.hpp"


namespace SAT {

using namespace Lib;

class ClauseSharing
{
public:
  SATClause* insert(SATClause* c);
  void wipe();

  static ClauseSharing* getInstance();

  SATClauseIterator content() { return pvi( ClauseSet::Iterator(_storage) ); }

private:
  struct Hasher {
    static unsigned hash(SATClause* t);
    static bool equals(SATClause* t1,SATClause* t2);
  };
  typedef Set<SATClause*, Hasher> ClauseSet;
  ClauseSet _storage;
};

};

#endif /* __ClauseSharing__ */
