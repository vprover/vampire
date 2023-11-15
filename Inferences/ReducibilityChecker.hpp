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

#include <bitset>

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class ReducibilityChecker {
private:
  DemodulationLHSIndex* _index;
  const Ordering& _ord;
  const Options& _opt;
  struct ReducibilityEntry {
    ReducibilityEntry() : reducesTo(), reduced(), rest(1), superTerms(), valid(false) {
      rest.push(VarOrder());
    }
    Stack<TermList> reducesTo;
    Stack<VarOrder> reduced;
    Stack<VarOrder> rest;
    Stack<Term*> superTerms;
    bool valid;
  };

  struct BinaryVarOrder {
    BinaryVarOrder() : _x(0), _y(0), _c(PoComp::INC) {}
    BinaryVarOrder(unsigned x, unsigned y, PoComp c)
      : _x(x < y ? x : y), _y(x < y ? y : x), _c(x < y ? c : reverse(c))
    {
      ASS_NEQ(_x,_y);
      ASS(_c!=PoComp::INC);
    }
    unsigned _x;
    unsigned _y;
    PoComp _c;
    vstring toString() const
    {
      return "X" + Int::toString(_x) + " " + Kernel::toString(_c) + " X" + Int::toString(_y);
    }
    bool operator!=(const BinaryVarOrder& other) const {
      return _x!=other._x || _y!=other._y || _c!=other._c;
    }
    bool operator==(const BinaryVarOrder& other) const {
      return _x==other._x && _y==other._y && _c==other._c;
    }

    struct Hash {
      static unsigned hash(const BinaryVarOrder& bvo) {
        return HashUtils::combine(bvo._x,bvo._y,static_cast<unsigned>(bvo._c));
      }
      static bool equals(const BinaryVarOrder& bvo1, const BinaryVarOrder& bvo2) {
        return bvo1._x==bvo2._x && bvo1._y==bvo2._y && bvo1._c==bvo2._c;
      }
    };
  };

  struct ReducibilityEntry2 {
    ReducibilityEntry2() : reducesTo(), reducesToCond(), reducedUnder(), reduced(false), superTerms(), valid(false) {}
    void addReducedUnder(unsigned x, unsigned y, std::bitset<3> b) {
      ASS_L(x,y);
      std::bitset<3>* ptr;
      reducedUnder.getValuePtr(std::make_pair(x,y), ptr);
      (*ptr) |= b;
    }
    static std::bitset<3> toBitset(PoComp c) {
      std::bitset<3> res;
      switch (c)
      {
      case PoComp::GT:
        res[0] = true;
        break;
      case PoComp::EQ:
        res[1] = true;
        break;
      case PoComp::LT:
        res[2] = true;
        break;
      default:
        ASSERTION_VIOLATION;
        break;
      }
      return res;
    }

    DHSet<TermList> reducesTo;
    DHMap<BinaryVarOrder,TermList,BinaryVarOrder::Hash,BinaryVarOrder::Hash> reducesToCond;
    DHMap<std::pair<unsigned,unsigned>,std::bitset<3>> reducedUnder;
    bool reduced;
    Stack<Term*> superTerms;
    bool valid;
  };

  TermSubstitutionTree _tis;
  DHMap<Clause*,Stack<VarOrder>> _demodulatorCache;
  DHMap<std::pair<TermList,TermList>,bool> _uselessLHSCache;

  DHMap<std::pair<unsigned,unsigned>,std::bitset<3>> _binaries;
  DHSet<Term*> _attempted;

  bool getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS);
  ReducibilityEntry* isTermReducible(Term* t);
  ReducibilityEntry2* getCacheEntryForTerm(Term* t);

  static BinaryVarOrder getBVOFromVO(const VarOrder& vo);
  static VarOrder getVOFromBVO(const BinaryVarOrder& bvo);
  bool updateBinaries(unsigned x, unsigned y, const std::bitset<3>& bv);

  bool checkSmaller(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult, vstringstream& exp);
  bool checkSmaller2(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmaller3(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);
  bool checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLit, Term* rwTermS, TermList* tgtTermS, vstringstream& exp);

public:
  CLASS_NAME(ReducibilityChecker);
  USE_ALLOCATOR(ReducibilityChecker);

  ReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt);

  void reset() {
    _binaries.reset();
    _attempted.reset();
  }

  bool checkSup(Clause* rwClause, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult);
  bool checkBR(Clause* queryClause, Clause* resultClause, ResultSubstitution* subst);
  bool checkLiteral(Literal* lit);
  void clauseActivated(Clause* cl);
  void preprocessClause(Clause* cl);
  bool* isUselessLHS(TermList lhs, TermList rhs) {
    return _uselessLHSCache.findPtr(std::make_pair(lhs,rhs));
  }
};

}

#endif