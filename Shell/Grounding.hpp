
/*
 * File Grounding.hpp.
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
 * @file Grounding.hpp
 * Defines class Grounding.
 */

#ifndef __Grounding__
#define __Grounding__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Shell
{

using namespace Kernel;
using namespace Lib;

class Grounding
{
public:
  static ClauseList* simplyGround(ClauseIterator clauses);

  ClauseList* ground(Clause* clause);


  static ClauseList* getEqualityAxioms(bool otherThanReflexivity);
private:
  static void getLocalEqualityAxioms(unsigned sort, bool otherThanReflexivity, ClauseList*& acc);


  struct GroundingApplicator
  {
    GroundingApplicator();
    void initForClause(Clause* cl);
    bool newAssignment();
    TermList apply(unsigned var);
  private:
    DHMap<unsigned, unsigned, IdentityHash> _varNumbering;
    Stack<TermList> _constants;
    DArray<unsigned> _indexes;
    unsigned _maxIndex;
    int _varCnt;
    bool _beforeFirst;
  };


  GroundingApplicator _ga;
};

}

#endif /* __Grounding__ */
