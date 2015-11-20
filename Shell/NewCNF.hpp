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
  Lib::Deque<Kernel::Formula*> _queue;

  typedef std::pair<Kernel::Formula*, bool> GenLit; // positive occurrences are true

  // generalized clause
  struct GenClause {
    CLASS_NAME(NewCNF::GenClause);
    USE_ALLOCATOR(NewCNF::GenClause);

    bool valid;
    Lib::DArray<GenLit> lits; // TODO: remove the extra indirection

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

  GenClauses _genClauses;

  typedef std::pair<SPGenClause,GenClauses::iterator> SPGenClauseLookup;

  typedef Lib::List<SPGenClauseLookup> SPGenClauseLookupList;

  struct OccInfo {
    // exact counts
    unsigned posCnt;
    unsigned negCnt;

    unsigned& cnt(bool positive) { return positive ? posCnt : negCnt; }

    // may contain pointers to invalidated GenClauses
    SPGenClauseLookupList* posOccs;
    SPGenClauseLookupList* negOccs;

    SPGenClauseLookupList*& occs(bool positive) { return positive ? posOccs : negOccs; }

    // constructor for an empty OccInto
    OccInfo() : posCnt(0), negCnt(0), posOccs(nullptr), negOccs(nullptr) {}
  };

  Lib::DHMap<Kernel::Formula*, OccInfo> _occurences;

  void processAll();
  void processAndOr(Kernel::Formula* g, OccInfo& occInfo);
  void processIffXor(Kernel::Formula* g, OccInfo& occInfo);

  void createClauses(Lib::Stack<Kernel::Clause*>& output);

}; // class NewCNF

}
#endif
