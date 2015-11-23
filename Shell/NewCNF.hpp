/**
 * @file NewCNF.hpp
 * Defines class NewCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#ifndef __NEWCNF__
#define __NEWCNF__

#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/DHMap.hpp"
#include "Kernel/Substitution.hpp"

namespace Kernel {
  class Formula;
  class FormulaUnit;
  class Clause;
  class Unit;
  class Literal;
};

#include <list>

namespace Shell {

/**
 * Class implementing the NewCNF transformation.
 * @since 19/11/2015 Manchester
 */
class NewCNF
{
public:
  void clausify (Kernel::FormulaUnit* unit,Lib::Stack<Kernel::Clause*>& output);
private:
  /**
   * Queue of formulas to process.
   *
   * Although queue sounds reasonable, the algorithm works with any order of the elements here.
   * Prioritizing should respect sub-formula relation,
   * and the algorithm will work better if subformulas are recognized.
   * However, not merging distinct occurrences of a single subformula
   * from the input does not compromise correctness.
   */
  Lib::Deque<Kernel::Formula*> _queue;

  // generalized literal
  typedef std::pair<Kernel::Formula*, bool> GenLit; // positive occurrences have second component true

  // generalized clause
  struct GenClause {
    CLASS_NAME(NewCNF::GenClause);
    USE_ALLOCATOR(NewCNF::GenClause);

    bool valid; // used for lazy deletion from OccInfo(s); see below

    Lib::DArray<GenLit> lits; // TODO: remove the extra indirection and allocate inside GenClause

    // constructor for a singleton GenClause
    GenClause(Kernel::Formula* f) : valid(true), lits(1) {
      lits[0] = make_pair(f,true);
    }

    // constructor for a GenClause of a given size -- lits need to be filled manually
    GenClause(unsigned size) : valid(true), lits(size) {}

    ~GenClause() {
      // TODO: print something to see it was destroyed
    }
  };

  typedef SmartPtr<GenClause> SPGenClause;

  typedef std::list<SPGenClause,STLAllocator<SPGenClause>> GenClauses;

  /**
   * Collection of the current set of generalized clauses.
   * (It is a doubly-linked list for constant time deletion.)
   */
  GenClauses _genClauses;

  struct SPGenClauseLookup {
    SPGenClause gc;
    GenClauses::iterator gci; // the iterator is only valid if the smart pointer points to a valid GenClause
    unsigned idx;             // index into lits of GenClause where the formula occurs
    SPGenClauseLookup(SPGenClause gc, GenClauses::iterator gci, unsigned idx) : gc(gc), gci(gci), idx(idx) {}
  };

  typedef Lib::List<SPGenClauseLookup> SPGenClauseLookupList;

  struct OccInfo {
    // may contain pointers to invalidated GenClauses
    SPGenClauseLookupList* posOccs;
    SPGenClauseLookupList* negOccs;

    SPGenClauseLookupList*& occs(bool positive) { return positive ? posOccs : negOccs; }

    // exact counts
    unsigned posCnt;
    unsigned negCnt;

    unsigned& cnt(bool positive) { return positive ? posCnt : negCnt; }

    // constructor for an empty OccInto
    OccInfo() : posOccs(nullptr), negOccs(nullptr), posCnt(0), negCnt(0) {}
  };

  Lib::DHMap<Kernel::Formula*, OccInfo> _occurences;

  void processAll();
  void processLiteral(Kernel::Formula* g, OccInfo& occInfo);
  void processAndOr(Kernel::Formula* g, OccInfo& occInfo);
  void processIffXor(Kernel::Formula* g, OccInfo& occInfo);
  void processForallExists(Kernel::Formula* g, OccInfo& occInfo);

  void createClauses(Lib::Stack<Kernel::Clause*>& output);

}; // class NewCNF

}
#endif
