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
 * @file SubstitutionCoverTree.hpp
 * Defines class SubstitutionCoverTree.
 */

#ifndef __SubstitutionCoverTree__
#define __SubstitutionCoverTree__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"
#include "CodeTreeInterfaces.hpp"


namespace Indexing {

using namespace Lib;

class SubstitutionCoverTree
{
public:
  SubstitutionCoverTree(Clause* cl);
  bool checkAndInsert(ResultSubstitution* subst, bool result, bool doInsert);
private:
  DHMap<unsigned,TermList> _varSorts;
  unsigned _fn;
  CodeTreeTIS _tis;
};

};

#endif // __SubstitutionCoverTree__
