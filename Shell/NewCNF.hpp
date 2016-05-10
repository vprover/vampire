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

#undef LOGGING
#define LOGGING 0

#if LOGGING
#define LOG1(arg)         cout << arg << endl;
#define LOG2(a1,a2)       cout << a1 << " " << a2 << endl;
#define LOG3(a1,a2,a3)    cout << a1 << " " << a2 << " " << a3 << endl;
#define LOG4(a1,a2,a3,a4) cout << a1 << " " << a2 << " " << a3 << " " << a4 << endl;
#else
#define LOG1(arg)
#define LOG2(a1,a2)
#define LOG3(a1,a2,a3)
#define LOG4(a1,a2,a3,a4)
#endif

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

  void clausify(FormulaUnit* unit, Stack<Clause*>& output);
private:
  unsigned _namingThreshold;

  FormulaUnit* _beingClausified;

  /**
   * Queue of formulas to process.
   *
   * Although queue sounds reasonable, the algorithm works with any order of the elements here.
   * Prioritizing should respect sub-formula relation,
   * and the algorithm will work better if subformulas are recognized.
   * However, not merging distinct occurrences of a single subformula
   * from the input does not compromise correctness.
   */
  Deque<Formula*> _queue;

  typedef pair<unsigned, Term*> Binding; // used for skolem bindings of the form <existential variable z, corresponding Skolem term f_z(U,V,...) >

  typedef List<Binding> BindingList;

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
  typedef pair<Formula*, SIGN> GenLit;

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

    DArray<GenLit> _literals; // TODO: remove the extra indirection and allocate inside GenClause
    unsigned _size;

    struct Iterator {
      Iterator(DArray<GenLit>::Iterator iter, unsigned left) : _iter(iter), _left(left) {}

      bool hasNext() {
        if (_left == 0) return false;
        return _iter.hasNext();
      }

      GenLit next() {
        _left--;
        return _iter.next();
      }

      private:
        DArray<GenLit>::Iterator _iter;
        unsigned _left;
    };

    Iterator genLiterals() {
      return Iterator(DArray<GenLit>::Iterator(_literals), _size);
    }

    unsigned size() {
      return _size;
    }

    // Position of a gen literal in _genClauses
    list<SmartPtr<GenClause>,STLAllocator<SmartPtr<GenClause>>>::iterator iter;

    vstring toString() {
      vstring res = "GC("+Int::toString(size())+")";
      if (!valid) {
        res += " [INVALID]";
      }
      Iterator gls = genLiterals();
      while (gls.hasNext()) {
        GenLit gl = gls.next();
        res += (sign(gl) == POSITIVE ? " {T} " : " {F} ") + formula(gl)->toString();
      }
      BindingList::Iterator bIt(bindings);
      while(bIt.hasNext()) {
        Binding b = bIt.next();
        res += " | X"+Int::toString(b.first)+" --> "+b.second->toString();
      }

      return res;
    }

    // constructor for a GenClause of a given size and given bindings -- lits need to be filled manually
    GenClause(unsigned size, BindingList* bindings) : valid(true), bindings(bindings), _literals(size), _size(0) {
      // cout << "+GenClause GC("<<size<<")"<< endl;
    }

    ~GenClause() {
      // cout << "-GenClause " << toString() << endl;
    }
  };

  typedef SmartPtr<GenClause> SPGenClause;

  void toClauses(SPGenClause gc, Stack<Clause*>& output);
  bool mapSubstitution(List<GenLit>* gc, Substitution subst, List<GenLit>* output);
  Clause* toClause(SPGenClause gc);

  typedef list<SPGenClause,STLAllocator<SPGenClause>> GenClauses;

  DHMap<Literal*, SIGN> _literalsCache;
  inline void pushLiteral(SPGenClause gc, GenLit gl) {
    CALL("NewCNF::pushLiteral");

    if (formula(gl)->connective() == LITERAL) {
      Literal* l = formula(gl)->literal();
      if (l->shared() && ((SIGN)l->polarity() != POSITIVE)) {
        Literal* cl = Literal::complementaryLiteral(l);
        gl = GenLit(new AtomicFormula(cl), OPPOSITE(sign(gl)));
      }
    }

    Formula* f = formula(gl);

    if (f->connective() == LITERAL && f->literal()->shared()) {
      Literal* l = f->literal();
      if (l->shared() && !_literalsCache.insert(l, sign(gl))) {
        if (sign(gl) != _literalsCache.get(l)) {
          gc->valid = false;
        } else {
          LOG2("Found duplicate literal", l->toString());
          return;
        }
      }
    } else {
      Occurrences* occurrences = _occurrences.findPtr(f);
      if (occurrences) {
        occurrences->add(Occurrence(gc, gc->_size));
      }
    }

    gc->_literals[gc->_size++] = gl;
  }

  /**
   * Collection of the current set of generalized clauses.
   * (It is a doubly-linked list for constant time deletion.)
   */
  GenClauses _genClauses;

  struct Occurrence {
    CLASS_NAME(NewCNF::Occurrence);
    USE_ALLOCATOR(NewCNF::Occurrence);

    SPGenClause gc;
    unsigned position;

    Occurrence(SPGenClause gc, unsigned position) : gc(gc), position(position) {}

    inline SIGN sign() {
      return gc->_literals[position].second;
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

      bool negateOccurrenceSign = false;
      if (f->connective() == LITERAL) {
        Literal* l = f->literal();
        if (l->shared() && ((SIGN)l->polarity() != POSITIVE)) {
          f = new AtomicFormula(Literal::complementaryLiteral(l));
          negateOccurrenceSign = true;
        }
      }

      while (occit.hasNext()) {
        Occurrence occ = occit.next();
        GenLit& gl = occ.gc->_literals[occ.position];
        formula(gl) = f;
        if (negateOccurrenceSign) {
          sign(gl) = OPPOSITE(sign(gl));
        }
      }
    }

    class Iterator {
    public:
      Iterator(Occurrences &occurrences): _iterator(List<Occurrence>::DelIterator(occurrences._occurrences)) {}

      inline bool hasNext() {
        while (_iterator.hasNext()) {
          Occurrence occ = _iterator.next();
          if (!occ.gc->valid) {
            _iterator.del();
            continue;
          }
          _current = SmartPtr<Occurrence>(new Occurrence(occ.gc, occ.position));
          return true;
        }
        return false;
      }
      Occurrence next() {
        return *_current;
      }
    private:
      List<Occurrence>::DelIterator _iterator;
      SmartPtr<Occurrence> _current;
    };

  private:
    // may contain pointers to invalidated GenClauses
    List<Occurrence>* _occurrences;
    unsigned _size;
  };

  SPGenClause makeGenClause(List<GenLit>* gls, BindingList* bindings) {
    SPGenClause gc = SPGenClause(new GenClause((unsigned)gls->length(), bindings));

    ASS(_literalsCache.isEmpty());

    List<GenLit>::Iterator glit(gls);
    while (glit.hasNext()) {
      pushLiteral(gc, glit.next());
    }

    _literalsCache.reset();

    return gc;
  }

  void introduceGenClause(List<GenLit>* gls, BindingList* bindings) {
    SPGenClause gc = makeGenClause(gls, bindings);

    if (gc->size() != (unsigned)gls->length()) {
      LOG4("Eliminated", gls->length() - gc->size(), "duplicate literal(s) from", gc->toString());
    }

    if (gc->valid) {
      _genClauses.push_front(gc);
      gc->iter = _genClauses.begin();
    } else {
      LOG2(gc->toString(), "is eliminated as it contains a tautology");
    }
  }

  void introduceGenClause(GenLit gl, BindingList* bindings=BindingList::empty()) {
    introduceGenClause(new List<GenLit>(gl), bindings);
  }

  void introduceGenClause(GenLit gl0, GenLit gl1, BindingList* bindings=BindingList::empty()) {
    introduceGenClause(new List<GenLit>(gl0, new List<GenLit>(gl1)), bindings);
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, List<GenLit>* gls) {
    CALL("NewCNF::introduceExtendedGenClause(SPGenClause, unsigned, List<GenLit>*)");

    LOG4("introduceExtendedGenClause:", gc->toString(), position, gls->length());

    unsigned size = gc->size() + gls->length() - 1;
    SPGenClause newGc = SPGenClause(new GenClause(size, gc->bindings));

    ASS(_literalsCache.isEmpty());

    GenClause::Iterator gcit = gc->genLiterals();
    unsigned i = 0;
    while (gcit.hasNext()) {
      GenLit gl = gcit.next();
      if (i == position) {
        List<GenLit>::Iterator glit(gls);
        while (glit.hasNext()) {
          pushLiteral(newGc, glit.next());
        }
      } else {
        pushLiteral(newGc, gl);
      }
      i++;
    }

    _literalsCache.reset();

    if (newGc->size() != size) {
      LOG4("Eliminated", size - newGc->size(), "duplicate literal(s) from", newGc->toString());
    }

    if (newGc->valid) {
      _genClauses.push_front(newGc);
      newGc->iter = _genClauses.begin();
    } else {
      LOG2(newGc->toString(), "is eliminated as it contains a tautology");
    }
  }

  void removeGenLit(SPGenClause gc, unsigned position) {
    introduceExtendedGenClause(gc, position, List<GenLit>::empty());
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, GenLit replacement) {
    introduceExtendedGenClause(gc, position, new List<GenLit>(replacement));
  }

  void introduceExtendedGenClause(SPGenClause gc, unsigned position, GenLit replacement, GenLit extension) {
    introduceExtendedGenClause(gc, position, new List<GenLit>(replacement, new List<GenLit>(extension)));
  }

  Occurrence pop(Occurrences &occurrences) {
    CALL("NewCNF::pop");

    Occurrence occ = occurrences.pop();
    occ.gc->valid = false;
    _genClauses.erase(occ.gc->iter);

    GenClause::Iterator glit = occ.gc->genLiterals();
    while (glit.hasNext()) {
      GenLit gl = glit.next();
      Formula* f = formula(gl);

      if (f->connective() == LITERAL && f->literal()->shared()) continue;

      Occurrences* fOccurrences = _occurrences.findPtr(f);
      if (fOccurrences) {
        fOccurrences->decrement();
      }
    }

    return occ;
  }

  DHMap<Formula*, Occurrences> _occurrences;

  /** map var --> sort */
  DHMap<unsigned,unsigned> _varSorts;

  void ensureHavingVarSorts();

  typedef const SharedSet<unsigned> VarSet;

  Term* createSkolemTerm(unsigned var, VarSet* free);

  // caching of free variables for subformulas
  DHMap<Formula*,VarSet*> _freeVars;
  VarSet* freeVars(Formula* g);

  // two level caching scheme for quantifier bindings
  // reset after skolemizing a particular subformula
  DHMap<BindingList*,BindingList*> _skolemsByBindings;
  DHMap<VarSet*,BindingList*>      _skolemsByFreeVars;

  void skolemise(QuantifiedFormula* g, BindingList* &bindings);

  Literal* createNamingLiteral(Formula* g, List<unsigned>* free);
  void nameSubformula(Formula* g, Occurrences &occurrences);

  void enqueue(Formula* formula, Occurrences occurrences = Occurrences()) {
    if ((formula->connective() == LITERAL) && formula->literal()->shared()) return;
    _queue.push_back(formula);
    if (!_occurrences.insert(formula, occurrences)) {
      ASSERTION_VIOLATION_REP(formula->toString());
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
  void processConstant(bool constant, Occurrences &occurrences);
  void processBoolVar(SIGN sign, unsigned var, Occurrences &occurrences);
  void processITE(Formula* condition, Formula* thenBranch, Formula* elseBranch, Occurrences &occurrences);
  void processLet(unsigned symbol, Formula::VarList*bindingVariables, TermList binding, TermList contents, Occurrences &occurrences);

  TermList nameLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, TermList contents);
  TermList inlineLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, TermList contents);

  TermList findITEs(TermList ts, Stack<unsigned> &variables, Stack<Formula*> &conditions,
                                 Stack<TermList> &thenBranches, Stack<TermList> &elseBranches);

  unsigned createFreshVariable(unsigned sort);

  bool shouldInlineITE(unsigned iteCounter);
}; // class NewCNF

}
#endif
