
/*
 * File SATClauseSharing.hpp.
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
 * @file SATClauseSharing.hpp
 * Defines class SATClauseSharing.
 */


#ifndef __SATClauseSharing__
#define __SATClauseSharing__

#include "Debug/Assertion.hpp"

#include "Lib/Set.hpp"
#include "Lib/VirtualIterator.hpp"

#include "SATClause.hpp"


namespace SAT {

using namespace Lib;

class SATClauseSharing
{
public:
  SATClause* insert(SATClause* c);
  void wipe();

  static SATClauseSharing* getInstance();

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

#endif /* __SATClauseSharing__ */
