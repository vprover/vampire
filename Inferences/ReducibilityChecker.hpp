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
 * @file ReducibilityChecker.hpp
 * Defines class ReducibilityChecker.
 */

#ifndef __ReducibilityChecker__
#define __ReducibilityChecker__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "Kernel/VarOrder.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class ReducibilityChecker {
private:
  DemodulationLHSIndex* _index;
  const Ordering& _ord;
  const Options& _opt;
  struct VarOrders {
    VarOrders() : reducesTo(), reduced(), rest(1), superTerms(), valid(false) {
      rest.push(VarOrder());
    }
    Stack<TermList> reducesTo;
    Stack<VarOrder> reduced;
    Stack<VarOrder> rest;
    Stack<Term*> superTerms;
    bool valid;
  };
  DHMap<Term*,VarOrders> _cache;
  TermSubstitutionTree _tis;
  DHMap<Clause*,Stack<VarOrder>> _demodulatorCache;
  DHMap<std::pair<TermList,TermList>,bool> _uselessLHSCache;

  bool getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS);
  VarOrders* isTermReducible(Term* t);

  bool checkSmaller(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult, vstringstream& exp);
  bool checkSmaller2(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLit, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);

  // bool kboGreater(TermList tl1, TermList tl2, const VarOrder& vo, const DHSet<unsigned>& vars);

public:
  CLASS_NAME(ReducibilityChecker);
  USE_ALLOCATOR(ReducibilityChecker);

  ReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt);

  bool check(Clause* rwClause, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult);
  bool checkBR(Clause* queryClause, Clause* resultClause, ResultSubstitution* subst);
  void clauseActivated(Clause* cl);
  void preprocessClause(Clause* cl);
  bool* isUselessLHS(TermList lhs, TermList rhs) {
    return _uselessLHSCache.findPtr(std::make_pair(lhs,rhs));
  }
};

}

#endif