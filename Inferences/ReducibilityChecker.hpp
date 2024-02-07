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

    DHSet<std::pair<TermList,TermList>> reducesTo;
    DHMap<std::pair<TermList,TermList>,VarOrderBV> reducesToCond;
    Stack<Term*> superTerms;
  };
private:
  TermSubstitutionTree _tis;

  DHMap<unsigned,TermList> _subst;
  bool _substRenaming;
  unsigned _varmap;

  DHSet<Term*> _attempted;
  VarOrderBV _reducedUnder;
  Stack<std::pair<TermList,Term*>> _sidesToCheck;
  void* _rwTermState;
  DHMap<std::pair<Term*,Literal*>,uint64_t> _reducedLitCache;
  DHMap<std::pair<Term*,Literal*>,Stack<VarOrder>> _reducedLitCache2;

  bool pushSidesFromLiteral(Literal* lit, ResultSubstitution* subst, bool result, Term* rwTermS, bool& litIncomparable);
  bool getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS, SplitSet* ss);
  ReducibilityEntry* getCacheEntryForTerm(Term* t);

  bool checkSide(TermList side, Term* sideS, Term* rwTermS, TermList* tgtTermS, Term* rwTerm, ResultSubstitution* subst, bool result);

  // bool checkLiteralSanity(Literal* lit, Term* rwTermS/*, vstringstream& exp*/);
  // bool checkRwTermSanity(Term* rwTermS, TermList tgtTermS/*, vstringstream& exp*/);
  // bool checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS/*, vstringstream& exp*/);
  // bool checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLit, Term* rwTermS, TermList* tgtTermS/*, vstringstream& exp*/);

  bool checkSup(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit);
  bool checkSupExpensive(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit, SplitSet* rwSplitSet);
  bool checkBRExpensive(Literal* rwLit);

public:
  USE_ALLOCATOR(ReducibilityChecker);

  ReducibilityChecker(DemodulationLHSIndex* index, UnitClauseLiteralIndex* litIndex, const Ordering& ord, const Options& opt);

  void reset() {
    _subst.reset();
    _attempted.reset();
    _reducedUnder = 0;
    _sidesToCheck.reset();
  }

  bool checkInferenceLazy(Clause* cl);
  bool checkSupEager(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit);
  bool checkBREager(Literal* lit);
  void clauseActivated(Clause* cl);
};

}

#endif