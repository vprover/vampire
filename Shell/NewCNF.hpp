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
  NewCNF(unsigned namingThreshold) : _namingThreshold(namingThreshold) {}

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

  struct BindingGetVarFunctor
  {
    DECL_RETURN_TYPE(unsigned);
    OWN_RETURN_TYPE operator()(const Binding& b) { return b.first; }
  };

  #define SIGN bool
  #define POSITIVE true
  #define NEGATIVE false
  #define OPPOSITE(sign) (!(sign))

  #define SIDE unsigned
  #define LEFT 0u
  #define RIGHT 1u

  // generalized literal
  typedef std::pair<Formula*, SIGN> GenLit;
  inline static Formula* &formula(GenLit &gl) {
    return gl.first;
  }
  inline static SIGN &sign(GenLit &gl) {
    return gl.second;
  }

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

    if (f->connective() == LITERAL && f->literal()->shared()) return;

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
    CLASS_NAME(NewCNF::Occurrences);
    USE_ALLOCATOR(NewCNF::Occurrences);

    SPGenClause gc;
    unsigned position;

    Occurrence(SPGenClause gc, unsigned position) : gc(gc), position(position) {}

    inline SIGN sign() {
      return gc->literals[position].second;
    }
  };

  class Occurrences {
  public:
    CLASS_NAME(NewCNF::Occurrences);
    USE_ALLOCATOR(NewCNF::Occurrences);

    Occurrences() : _occurrences(nullptr), _size(0) {}

    unsigned size() { return _size; }

    inline void add(Occurrence occ) {
      List<Occurrence>::push(occ, _occurrences);
      _size++;
    }

    bool isNonEmpty() {
      while (true) {
        if (List<Occurrence>::isEmpty(_occurrences)) {
          return false;
        }
        if (!_occurrences->head().gc->valid) {
          List<Occurrence>::pop(_occurrences);
        } else {
          return true;
        }
      }
    }

    void decrement() {
      _size--;
      ASS_GE(_size, 0);
    }

    Occurrence pop() {
      return List<Occurrence>::pop(_occurrences);
    }

    void replaceBy(Formula* f) {
      Occurrences::Iterator occit(*this);
      while (occit.hasNext()) {
        Occurrence occ = occit.next();
        GenLit& gl = occ.gc->literals[occ.position];
        formula(gl) = f;
      }
    }

    class Iterator {
    public:
      Iterator(Occurrences &occurrences): _iterator(List<Occurrence>::DelIterator(occurrences._occurrences)) {}

      inline bool hasNext() {
        return _iterator.hasNext();
//        while (true) {
//          if (_iterator.hasNext()) {
//            if (!_iterator.next().gc->valid) {
//              _iterator.del();
//            } else {
//              return true;
//            }
//          } else {
//            return false;
//          }
//        }
      }
      Occurrence next() {
        return _iterator.next();
      }
    private:
      List<Occurrence>::DelIterator _iterator;
    };

  private:
    // may contain pointers to invalidated GenClauses
    List<Occurrence>* _occurrences;
    unsigned _size;
  };

  SPGenClause introduceGenClause(unsigned size, BindingList* bindings) {
    SPGenClause gc = SPGenClause(new GenClause(size, bindings));
    _genClauses.push_front(gc);
    gc->iter = _genClauses.begin();
    return gc;
  }

  void introduceGenClause(GenLit gl) {
    SPGenClause gc = introduceGenClause(1, BindingList::empty());
    setLiteral(gc, 0, gl);
  }

  void introduceGenClause(GenLit gl0, GenLit gl1) {
    SPGenClause gc = introduceGenClause(2, BindingList::empty());
    setLiteral(gc, 0, gl0);
    setLiteral(gc, 1, gl1);
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, List<GenLit>*gls) {
    SPGenClause processedGc = introduceGenClause(gc->size() + gls->length() - 1, gc->bindings);
    for (unsigned i = 0, j = 0; i < gc->size(); i++) {
      if (i == position) {
        List<GenLit>::Iterator glit(gls);
        while (glit.hasNext()) {
          setLiteral(processedGc, j++, glit.next());
        }
      } else {
        setLiteral(processedGc, j++, gc->literals[i]);
      }
    }
  }

  void removeGenLit(SPGenClause gc, unsigned position) {
    introduceExtendedGenClause(gc, position, 0);
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, GenLit replacement) {
    introduceExtendedGenClause(gc, position, new List<GenLit>(replacement, 0));
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, GenLit replacement, GenLit extension) {
    introduceExtendedGenClause(gc, position, new List<GenLit>(replacement, new List<GenLit>(extension, 0)));
  }

  Occurrence pop(Occurrences &occurrences) {
    Occurrence occ = occurrences.pop();
    occ.gc->valid = false;
    _genClauses.erase(occ.gc->iter);
    for (unsigned i = 0; i < occ.gc->literals.size(); i++) {
      Formula* f = formula(occ.gc->literals[i]);

      if (f->connective() == LITERAL) continue;

      Occurrences* fOccurrences = _occurrences.findPtr(f);
      if (fOccurrences) {
        fOccurrences->decrement();
      }
    }
    return occ;
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

  void enqueue(Formula* formula, Occurrences occurrences = Occurrences()) {
    if (formula->connective() != LITERAL || !formula->literal()->shared()) {
      _queue.push_back(formula);
      if (!_occurrences.insert(formula, occurrences)) {
        ASSERTION_VIOLATION_REP(formula->toString());
      }
    }
  }

  void dequeue(Formula* &formula, Occurrences &occurrences) {
    formula = _queue.pop_front();
    ALWAYS(_occurrences.pop(formula,occurrences));
  }

  void process(Formula* g, Occurrences &occurrences);
  void process(JunctionFormula* g, Occurrences &occurrences);
  void process(BinaryFormula* g, Occurrences &occurrences);
  void process(QuantifiedFormula* g, Occurrences &occurrences);
  void process(TermList ts, Occurrences &occurrences);

  void process(Literal* l, Occurrences &occurrences);
  void processBoolVar(unsigned var, Occurrences &occurrences);
  void processITE(Formula* condition, Formula* thenBranch, Formula* elseBranch, Occurrences &occurrences);
  void processLet(unsigned symbol, Formula::VarList*bindingVariables, TermList binding, TermList contents, Occurrences &occurrences);

  TermList nameLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, TermList contents);

  TermList findSpecialTermData(TermList ts, Stack<Term*> &specialTerms, Stack<TermList> &names);

  TermList createNamingTerm(unsigned functor, IntList* vars);
}; // class NewCNF

}
#endif
