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
#include "Indexing/LiteralIndex.hpp"
#include "Kernel/VarOrder.hpp"

#include "InferenceEngine.hpp"

#include <bitset>

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class ReducibilityChecker {
private:
  DemodulationLHSIndex* _index;
  UnitClauseLiteralIndex* _litIndex;
  const Ordering& _ord;
  const Options& _opt;

public:
  struct ReducibilityEntry {
    ReducibilityEntry() : reducesTo(), reducesToCond(), superTerms() {}

    DHSet<std::pair<TermList,Term*>> reducesTo;
    DHMap<std::pair<TermList,Term*>,uint64_t> reducesToCond;
    Stack<Term*> superTerms;
  };
private:
  TermSubstitutionTree _tis;
  DHSet<Term*> _attempted;
  uint64_t _reducedUnder;
  Stack<Term*> _sidesToCheck;
  Stack<TermList> _sidesToCheck2;
  void* _rwTermState;
  Stack<std::tuple<unsigned,unsigned,bool>> _constraintsFromComparison;

  bool pushSidesFromLiteral(Literal* lit, ResultSubstitution* subst, bool result);
  bool getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS);
  ReducibilityEntry* getCacheEntryForTerm(Term* t);

  bool checkLiteral(Term* rwTermS, TermList* tgtTermS/*, vstringstream& exp*/, Term* rwTerm, ResultSubstitution* subst, bool result);

  bool checkLiteralSanity(Literal* lit, Term* rwTermS/*, vstringstream& exp*/);
  bool checkRwTermSanity(Term* rwTermS, TermList tgtTermS/*, vstringstream& exp*/);
  bool checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS/*, vstringstream& exp*/);
  bool checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLit, Term* rwTermS, TermList* tgtTermS/*, vstringstream& exp*/);

public:
  USE_ALLOCATOR(ReducibilityChecker);

  ReducibilityChecker(DemodulationLHSIndex* index, UnitClauseLiteralIndex* litIndex, const Ordering& ord, const Options& opt);

  void reset() {
    _attempted.reset();
    _reducedUnder = 0;
  }

  bool checkSup(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, Ordering::Result rwComp, bool eqClauseUnit);
  bool checkBR(Clause* queryClause, Clause* resultClause, ResultSubstitution* subst);
  bool checkLiteral(Literal* lit);
  void clauseActivated(Clause* cl);
};

}

#endif