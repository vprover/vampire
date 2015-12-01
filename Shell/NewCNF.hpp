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
#include "Lib/SharedSet.hpp"
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
  NewCNF(int namingThreshold) : _namingThreshold(namingThreshold) {}

  void clausify (Kernel::FormulaUnit* unit,Lib::Stack<Kernel::Clause*>& output);
private:
  unsigned _namingThreshold;

  Kernel::FormulaUnit* _beingClausified;

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

  typedef std::pair<unsigned, Kernel::Term*> Binding; // used for skolem bindings of the form <existential variable z, corresponding Skolem term f_z(U,V,...) >

  typedef Lib::List<Binding> BindingList;

  struct BindingGetFirstFunctor
  {
    DECL_RETURN_TYPE(unsigned);
    OWN_RETURN_TYPE operator()(const Binding& b) { return b.first; }
  };

  // generalized literal
  typedef std::pair<Kernel::Formula*, bool> GenLit; // positive occurrences have second component true

  // generalized clause
  struct GenClause {
    CLASS_NAME(NewCNF::GenClause);
    USE_ALLOCATOR(NewCNF::GenClause);

    bool valid; // used for lazy deletion from OccInfo(s); see below

    BindingList* bindings; // the list is not owned by the GenClause (they will shallow-copied and shared)
    // we could/should carry bindings on the GenLits-level; but GenClause seems sufficient as long as we are rectified

    Lib::DArray<GenLit> lits; // TODO: remove the extra indirection and allocate inside GenClause

    Lib::vstring toString() {
      Lib::vstring res = "GC("+Int::toString(lits.size())+")";
      for (unsigned i = 0; i < lits.size(); i++) {
        res += (lits[i].second ? " {T} " : " {F} ") + lits[i].first->toString();
      }
      BindingList::Iterator bIt(bindings);
      while(bIt.hasNext()) {
        Binding b = bIt.next();
        res += " X"+Int::toString(b.first)+" --> "+b.second->toString();
      }

      return res;
    }

    // constructor for a singleton GenClause
    GenClause(Kernel::Formula* f) : valid(true), bindings(BindingList::empty()), lits(1) {
      lits[0] = make_pair(f,true);

      // cout << "+GenClause GC(1)" << endl;
    }

    // constructor for a GenClause of a given size and given bindings -- lits need to be filled manually
    GenClause(unsigned size, BindingList* bindings) : valid(true), bindings(bindings), lits(size) {
      // cout << "+GenClause GC("<<size<<")"<< endl;
    }

    ~GenClause() {
      // cout << "-GenClause " << toString() << endl;
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

  /** map var --> sort */
  Lib::DHMap<unsigned,unsigned> _varSorts;

  void ensureHavingVarSorts();

  typedef const SharedSet<unsigned> VarSet;

  Kernel::Term* createSkolemTerm(unsigned var, VarSet* free);

  // caching of free variables for subformulas
  Lib::DHMap<Kernel::Formula*,VarSet*> _freeVars;
  VarSet* freeVars(Kernel::Formula* g);

  // two level caching scheme for quantifier bindings
  // reset after skolemizing a particular subformula
  Lib::DHMap<BindingList*,BindingList*> _skolemsByBindings;
  Lib::DHMap<VarSet*,BindingList*>      _skolemsByFreeVars;

  void skolemise(Kernel::Formula* g, BindingList*& bindings);

  Kernel::Literal* createNamingLiteral(Kernel::Formula* g, VarSet* free);
  Kernel::Formula* performNaming(Kernel::Formula* g, OccInfo& occInfo);

  void processAll();
  void processLiteral(Kernel::Formula* g, OccInfo& occInfo);
  void processAndOr(Kernel::Formula* g, OccInfo& occInfo);
  void processIffXor(Kernel::Formula* g, OccInfo& occInfo);
  void processForallExists(Kernel::Formula* g, OccInfo& occInfo);

  void createClauses(Lib::Stack<Kernel::Clause*>& output);

}; // class NewCNF

}
#endif
