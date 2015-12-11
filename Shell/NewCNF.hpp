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

  #define SIGN bool
  #define POSITIVE true
  #define NEGATIVE false
  #define OPPOSITE(sign) (!(sign))

  // generalized literal
  typedef std::pair<Formula*, SIGN> GenLit;
  inline Formula* &formula(GenLit gl) {
    return gl.first;
  }
  inline SIGN &sign(GenLit gl) {
    return gl.second;
  }
//  inline GenLit makeGenLit(Formula* f, SIGN sign) {
//    return make_pair(f, sign);
//  }

  // generalized clause
  struct GenClause {
    CLASS_NAME(NewCNF::GenClause);
    USE_ALLOCATOR(NewCNF::GenClause);

    bool valid; // used for lazy deletion from Occurrences(s); see below

    BindingList* bindings; // the list is not owned by the GenClause (they will shallow-copied and shared)
    // we could/should carry bindings on the GenLits-level; but GenClause seems sufficient as long as we are rectified

    Lib::DArray<GenLit> literals; // TODO: remove the extra indirection and allocate inside GenClause

    unsigned size() {
      return (unsigned) literals.size();
    }

    // Position of a gen literal in _genClauses
    std::list<SmartPtr<GenClause>,STLAllocator<SmartPtr<GenClause>>>::iterator iter;

    Lib::vstring toString() {
      Lib::vstring res = "GC("+Int::toString(literals.size())+")";
      for (unsigned i = 0; i < literals.size(); i++) {
        res += (literals[i].second ? " {T} " : " {F} ") + literals[i].first->toString();
      }
      BindingList::Iterator bIt(bindings);
      while(bIt.hasNext()) {
        Binding b = bIt.next();
        res += " X"+Int::toString(b.first)+" --> "+b.second->toString();
      }

      return res;
    }

    // constructor for a GenClause of a given size and given bindings -- lits need to be filled manually
    GenClause(unsigned size, BindingList* bindings) : valid(true), bindings(bindings), literals(size) {
      // cout << "+GenClause GC("<<size<<")"<< endl;
    }

    ~GenClause() {
      // cout << "-GenClause " << toString() << endl;
    }
  };

  typedef SmartPtr<GenClause> SPGenClause;

  Clause* toClause(SPGenClause gc);

  typedef std::list<SPGenClause,STLAllocator<SPGenClause>> GenClauses;

  inline void setLiteral(SPGenClause gc, unsigned position, GenLit gl) {
    Formula* f = formula(gl);
    gc->literals[position] = gl;

    if (f->connective() != LITERAL) return;

    Occurrences* occurrences = _occurrences.findPtr(f);
    if (occurrences) {
      occurrences->add(Occurrence(gc, position));
    }
  }

  /**
   * Collection of the current set of generalized clauses.
   * (It is a doubly-linked list for constant time deletion.)
   */
  GenClauses _genClauses;

  struct Occurrence {
    SPGenClause gc;
    unsigned position;

    Occurrence(SPGenClause gc, unsigned position) : gc(gc), position(position) {}

    inline SIGN sign() {
      return gc->literals[position].second;
    }
  };

  typedef Lib::List<Occurrence> OccurrenceList;

  class Occurrences {
  public:
    Occurrences(GenClauses* genClauses) : _genClauses(genClauses), _occurrences(nullptr), _count(0) {}

    unsigned count() { return _count; }

    Lib::List<Occurrence>* &occurrences() {
      return _occurrences;
    }

    inline void add(Occurrence occ) {
      _occurrences = new OccurrenceList(occ, _occurrences);
      _count++;
    }

    bool isNonEmpty() {
      while (true) {
        if (OccurrenceList::isEmpty(_occurrences)) {
          return false;
        }
        if (!_occurrences->head().gc->valid) {
          OccurrenceList::pop(_occurrences);
        } else {
          return true;
        }
      }
    }

    void setTail(OccurrenceList* occurrences) {
      _occurrences = _occurrences->setTail(occurrences);
    }

    void set(OccurrenceList* occurrences) {
      _occurrences = occurrences;
    }

    Occurrence head() {
      return _occurrences->head();
    }

    Occurrence pop() {
      Occurrence occ = OccurrenceList::pop(_occurrences);

      occ.gc->valid = false;
      _count -= occ.gc->literals.size();
      ASS_GE(_count, 0);

      _genClauses->erase(occ.gc->iter);

      return occ;
    }

  private:
    static GenClauses* _genClauses;

    // may contain pointers to invalidated GenClauses
    OccurrenceList* _occurrences;

    // the number of valid clauses in positiveOccurrences and negativeOccurrences
    // this is in general not equal to the size of positiveOccurrences and negativeOccurrences
    unsigned _count;
  };

  SPGenClause introduceGenClause(unsigned size, BindingList* bindings=BindingList::empty()) {
    SPGenClause gc = SPGenClause(new GenClause(size, bindings));
    _genClauses.push_front(gc);
    gc->iter = _genClauses.begin();
    return gc;
  }

  Lib::DHMap<Kernel::Formula*, Occurrences> _occurrences;

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

  void skolemise(QuantifiedFormula* g, BindingList* &bindings);

  Kernel::Literal* createNamingLiteral(Formula* g, VarSet* free);
  Kernel::Formula* nameSubformula(Formula* g, Occurrences &occInfo);

  void enqueue(Formula* formula, Occurrences occurrences = Occurrences(&_genClauses)) {
    if (formula->connective() != LITERAL) {
      _queue.push_back(formula);
      ALWAYS(_occurrences.insert(formula, occurrences));
    }
  }

  void dequeue(Formula* &formula, Occurrences &occurrences) {
    formula = _queue.pop_front();
    ALWAYS(_occurrences.pop(formula,occurrences));
  }

  void process();
  void process(JunctionFormula* g, Occurrences &occurrences);
  void process(BinaryFormula* g, Occurrences &occurrences);
  void process(QuantifiedFormula* g, Occurrences &occurrences);

}; // class NewCNF

}
#endif
