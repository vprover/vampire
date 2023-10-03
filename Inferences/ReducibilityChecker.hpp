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

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;

class ReducibilityChecker {
private:
  DemodulationLHSIndex* _index;
  const Ordering& _ord;
  const Options& _opt;

  // VarOrders checkTerm(Term* t, Term* tS, Term* rwTermS, const DHSet<unsigned>& vars);
  // VarOrders checkTermReducible(Term* tS, TermList* tgtTermS, bool greater, const VarOrders& initial);
  // bool checkSmaller(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, bool greater, vstringstream& exp);
  bool checkSmaller(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLit, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);

  // bool kboGreater(TermList tl1, TermList tl2, const VarOrder& vo, const DHSet<unsigned>& vars);

public:
  CLASS_NAME(ReducibilityChecker);
  USE_ALLOCATOR(ReducibilityChecker);

  ReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt);

  void preprocessClause(Clause* cl);
  bool check(Clause* rwClause, Clause* eqClause, Literal* rwLitS, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool eqIsResult);
};

}

#endif