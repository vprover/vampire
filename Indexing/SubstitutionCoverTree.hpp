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
  : public CodeTree
{
public:
  SubstitutionCoverTree(Clause* cl);
  bool checkAndInsert(const Ordering* ord, ResultSubstitution* subst, bool result, bool doInsert=false, Term* lhs=nullptr, Term* rhs=nullptr);
private:
  void insert(const TermStack& ts, void* ptr);
  bool check(const TermStack& ts, const Ordering* ord);

  DHMap<unsigned,TermList> _varSorts;
  // unsigned _fn;
  // CodeTreeTIS _tis;

  struct LeafData {
    Term* lhs = nullptr;
    Term* rhs = nullptr;
  };

  struct SubstMatcher
  : public Matcher
  {
    void init(CodeTree* tree, const TermStack& ts);
    void reset();

    LeafData* next();
  };
};

};

#endif // __SubstitutionCoverTree__
