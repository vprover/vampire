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
#include "Kernel/Formula.hpp" //TODO AYB remove, it is not required in master

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
  NewCNF(unsigned namingThreshold)
    : _namingThreshold(namingThreshold), _iteInliningThreshold((unsigned)ceil(log2(namingThreshold))),
      _collectedVarSorts(false), _maxVar(0),_forInduction(false) {}

  void clausify(FormulaUnit* unit, Stack<Clause*>& output);
  void setForInduction(){ _forInduction=true; }
private:
  unsigned _namingThreshold;
  unsigned _iteInliningThreshold;

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

  // all allocations of shared BindingLists should go via BindingStore so that they get destroyed in the end
  struct BindingStore {
    void pushAndRemember(Binding b, BindingList* &lst) {
      lst = new BindingList(b,lst);
      _stored.push(lst);
    }
    void pushAndRememberWhileApplying(Binding b, BindingList* &lst);
    ~BindingStore() {
      Stack<BindingList*>::Iterator it(_stored);
      while(it.hasNext()) {
        BindingList* cell = it.next();
        delete cell;
      }
    }
  private:
    Stack<BindingList*> _stored;
  };

  BindingStore _bindingStore;
  BindingStore _foolBindingStore;

  struct BindingGetVarFunctor
  {
    unsigned operator()(const Binding& b) { return b.first; }
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
  typedef pair<Literal*, List<GenLit>*> LPair;

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

    GenClause(unsigned size, BindingList* bindings, BindingList* foolBindings)
      : valid(true), bindings(bindings), foolBindings(foolBindings), _literals(size), _size(0) {}

    bool valid; // used for lazy deletion from Occurrences(s); see below

    BindingList* bindings; // the list is not owned by the GenClause (they will shallow-copied and shared)
    BindingList* foolBindings;
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
      BindingList::Iterator fbit(foolBindings);
      while(fbit.hasNext()) {
        Binding b = fbit.next();
        res += " | X"+Int::toString(b.first)+" ---> "+b.second->toString();
      }

      return res;
    }
  };

  typedef SmartPtr<GenClause> SPGenClause;

  void toClauses(SPGenClause gc, Stack<Clause*>& output);
  bool mapSubstitution(List<GenLit>* gc, Substitution subst, bool onlyFormulaLevel, List<GenLit>* &output);
  Clause* toClause(SPGenClause gc);

  typedef list<SPGenClause,STLAllocator<SPGenClause>> GenClauses;

  /**
   * pushLiteral is responsible for tautology elimination. Whenever it sees two
   * generalised literals with the opposite signs, the entire generalised clause
   * is discarded. Whenever it sees more than one occurrence of a generalised
   * literal, only one copy is kept.
   *
   * pushLiteral two kinds of tautologies: between shared literals and between
   * copies of formulas. The former is possible because syntactically
   * equivalent literals are shared and therefore can be compared by pointer.
   * The latter can occur after inlining of let-s and ite-s. Removing tautologies
   * between formulas is important for traversal of the list of occurrences,
   * without it popping the first occurrence of a formula will invalidate the
   * entire generalised clause, and other occurrences will never be seen.
   */
  DHMap<Literal*, SIGN> _literalsCache;
  DHMap<Formula*, SIGN> _formulasCache;
  inline void pushLiteral(SPGenClause gc, GenLit gl) {
    CALL("NewCNF::pushLiteral");

    if (formula(gl)->connective() == LITERAL) {
      /**
       * A generalised literal that is atomic have two signs, the one assigned
       * to the proper literal, and the one assigned to the generalised literal.
       *
       * To simplify tautology elimination we will always store proper literals
       * with the positive sign. Hence, proper literals with negative sign are
       * replaces with their complements.
       */
      Literal* l = formula(gl)->literal();
      if (l->shared() && ((SIGN)l->polarity() != POSITIVE)) {
        Literal* cl = Literal::complementaryLiteral(l);
        gl = GenLit(new AtomicFormula(cl), OPPOSITE(sign(gl)));
      }
    } else if (formula(gl)->connective() == NOT) {
      gl = GenLit(formula(gl)->uarg(), OPPOSITE(sign(gl)));
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
    } else if (!_formulasCache.insert(f, sign(gl))) {
      if (sign(gl) != _formulasCache.get(f)) {
        gc->valid = false;
      } else {
        LOG2("Found duplicate formula", f->toString());
        return;
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

  /**
   * Occurrences represents a list of occurrences in valid generalised clauses.
   * Occurrences is used instead of an obvious List<Occurrence> because it
   * maintains a (1) convenient (2) constant time size() method.
   *
   * (1) Occurrences maintains a List<Occurrence> * _occurrences, where each
   *     Occurrence points to a generalised clause which can become invalid.
   *     We are only interested in occurrences in valid generalised clauses.
   *     It wouldn't be enough to call _occurrences->length(), as it might
   *     count occurrences in invalid generalised clauses.
   *
   * (2) List::length is O(n) in the version of stdlib we are using. Instead of
   *     calling it we maintain the size in a variables (_size) that is updated
   *     in two situations:
   *     - whenever the list of occurrences changes (by calling Occurrences's
   *       own add(), append() and pop() methods)
   *     - whenever a generalised clause is invalidated. In that case NewCNF
   *       calls Occurrences::decrement() of every list of occurrences that has
   *       an occurrence in this newly invalid generalised clause
   */
  class Occurrences {
  private:
    List<Occurrence>* _occurrences;
    unsigned _size;

  public:
    CLASS_NAME(NewCNF::Occurrences);
    USE_ALLOCATOR(NewCNF::Occurrences);

    Occurrences() : _occurrences(nullptr), _size(0) {}

    unsigned size() { return _size; }

    inline void add(Occurrence occ) {
      List<Occurrence>::push(occ, _occurrences);
      _size++;
    }

    inline void append(Occurrences occs) {
      _occurrences = List<Occurrence>::concat(_occurrences, occs._occurrences);
      _size += occs.size();
    }

    bool isNonEmpty() {
      while (true) {
        if (List<Occurrence>::isEmpty(_occurrences)) {
          ASS_EQ(_size, 0);
          return false;
        }
        if (!_occurrences->head().gc->valid) {
          List<Occurrence>::pop(_occurrences);
        } else {
          ASS_G(_size, 0);
          return true;
        }
      }
    }

    void decrement() {
      ASS_G(_size, 0);
      _size--;
    }

    Occurrence pop() {
      ASS(isNonEmpty());
      Occurrence occ = List<Occurrence>::pop(_occurrences);
      ASS(occ.gc->valid);
      _size--;
      ASS_GE(_size, 0);
      return occ;
    }

    void replaceBy(Formula* f) {
      CALL("Occurrences::replaceBy");

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

    void invert() {
      CALL("Occurrences::invert");

      Occurrences::Iterator occit(*this);
      while (occit.hasNext()) {
        Occurrence occ = occit.next();
        GenLit& gl = occ.gc->_literals[occ.position];
        sign(gl) = OPPOSITE(sign(gl));
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
  };

  SPGenClause makeGenClause(List<GenLit>* gls, BindingList* bindings, BindingList* foolBindings) {
    SPGenClause gc = SPGenClause(new GenClause(List<GenLit>::length(gls), bindings, foolBindings));

    ASS(_literalsCache.isEmpty());
    ASS(_formulasCache.isEmpty());

    List<GenLit>::Iterator glit(gls);
    while (glit.hasNext()) {
      pushLiteral(gc, glit.next());
    }

    _literalsCache.reset();
    _formulasCache.reset();

    return gc;
  }

  void introduceGenClause(List<GenLit>* gls, BindingList* bindings, BindingList* foolBindings) {
    SPGenClause gc = makeGenClause(gls, bindings, foolBindings);

    if (gc->size() != List<GenLit>::length(gls)) {
      LOG4("Eliminated", List<GenLit>::length(gls) - gc->size(), "duplicate literal(s) from", gc->toString());
    }

    if (gc->valid) {
      _genClauses.push_front(gc);
      gc->iter = _genClauses.begin();

      GenClause::Iterator igl = gc->genLiterals();
      unsigned position = 0;
      while (igl.hasNext()) {
        GenLit gl = igl.next();
        Occurrences* occurrences = _occurrences.findPtr(formula(gl));
        if (occurrences) {
          occurrences->add(Occurrence(gc, position));
        }
        position++;
      }
    } else {
      LOG2(gc->toString(), "is eliminated as it contains a tautology");
    }
  }

  void introduceGenClause(GenLit gl, BindingList* bindings=BindingList::empty(), BindingList* foolBindings=BindingList::empty()) {
    introduceGenClause(new List<GenLit>(gl), bindings, foolBindings);
  }

  void introduceGenClause(GenLit gl0, GenLit gl1, BindingList* bindings=BindingList::empty(), BindingList* foolBindings=BindingList::empty()) {
    introduceGenClause(new List<GenLit>(gl0, new List<GenLit>(gl1)), bindings, foolBindings);
  }

  void introduceExtendedGenClause(Occurrence occ, List<GenLit>* gls) {
    CALL("NewCNF::introduceExtendedGenClause(Occurrence, List<GenLit>*)");

    SPGenClause gc = occ.gc;
    unsigned position = occ.position;

    unsigned size = gc->size() + List<GenLit>::length(gls) - 1;
    SPGenClause newGc = SPGenClause(new GenClause(size, gc->bindings, gc->foolBindings));

    ASS(_literalsCache.isEmpty());
    ASS(_formulasCache.isEmpty());

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
    _formulasCache.reset();

    if (newGc->size() != size) {
      LOG4("Eliminated", size - newGc->size(), "duplicate literal(s) from", newGc->toString());
    }

    if (newGc->valid) {
      _genClauses.push_front(newGc);
      newGc->iter = _genClauses.begin();

      GenClause::Iterator igl = newGc->genLiterals();
      unsigned position = 0;
      while (igl.hasNext()) {
        GenLit gl = igl.next();
        Occurrences* occurrences = _occurrences.findPtr(formula(gl));
        if (occurrences) {
          occurrences->add(Occurrence(newGc, position));
        }
        position++;
      }
    } else {
      LOG2(newGc->toString(), "is eliminated as it contains a tautology");
    }
  }

  void removeGenLit(Occurrence occ) {
    introduceExtendedGenClause(occ, List<GenLit>::empty());
  }

  void introduceExtendedGenClause(Occurrence occ, GenLit replacement) {
    // CHECK: leaking below?
    introduceExtendedGenClause(occ, new List<GenLit>(replacement));
  }

  void introduceExtendedGenClause(Occurrence occ, GenLit replacement, GenLit extension) {
    // CHECK: leaking below?
    introduceExtendedGenClause(occ, new List<GenLit>(replacement, new List<GenLit>(extension)));
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
  DHMap<unsigned,TermList> _varSorts;
  bool _collectedVarSorts;
  unsigned _maxVar;

  void ensureHavingVarSorts();

  Term* createSkolemTerm(unsigned var, VarSet* free, Formula *reuse);

  bool _forInduction;

  // caching of free variables for subformulas
  DHMap<Formula*,VarSet*> _freeVars;
  VarSet* freeVars(Formula* g);

  // two level caching scheme for quantifier bindings
  // reset after skolemizing a particular subformula
  DHMap<BindingList*,BindingList*> _skolemsByBindings;
  DHMap<VarSet*,BindingList*>      _skolemsByFreeVars;

  DHMap<BindingList*,BindingList*> _foolSkolemsByBindings;
  DHMap<VarSet*,BindingList*>      _foolSkolemsByFreeVars;

  // caching binding substitutions for the final phase of GenClause -> Clause transformation
  // this saves time, because bindings are potentially shared
  DHMap<BindingList*,Substitution*> _substitutionsByBindings;

  // do not provide definitions for names we've already seen (when -dr on)
  DHSet<Literal *> _already_seen[2];

  void skolemise(QuantifiedFormula* g, BindingList* &bindings, BindingList*& foolBindings);

  Literal* createNamingLiteral(Formula* g, VList* free);
  void nameSubformula(Formula* g, Occurrences &occurrences);

  void enqueue(Formula* formula, Occurrences occurrences = Occurrences()) {
    if ((formula->connective() == LITERAL) && formula->literal()->shared()) return;

    if (formula->connective() == NOT) {
      /**
       * Formulas are always stored without negations in genclauses,
       * therefore it is safe to drop the negation before queueing,
       * all the occurrences of the formula won't have it either
       */
      formula = formula->uarg();
      ASS_REP(formula->connective() != LITERAL, formula->toString());

      occurrences.invert();
    }

    if (_occurrences.find(formula)) {
      Occurrences oldOccurrences;
      _occurrences.pop(formula, oldOccurrences);
      occurrences.append(oldOccurrences);
    } else {
      _queue.push_back(formula);
    }
    ALWAYS(_occurrences.insert(formula, occurrences));
  }

  void dequeue(Formula* &formula, Occurrences &occurrences) {
    formula = _queue.pop_front();
    ALWAYS(_occurrences.pop(formula,occurrences));
  }

  void process(Formula* g, Occurrences &occurrences);
  void process(JunctionFormula* g, Occurrences &occurrences);
  void process(BinaryFormula* g, Occurrences &occurrences);
  void process(QuantifiedFormula* g, Occurrences &occurrences);

  void processBoolterm(TermList ts, Occurrences &occurrences);
  void process(Literal* l, Occurrences &occurrences);
  void processConstant(bool constant, Occurrences &occurrences);
  void processBoolVar(SIGN sign, unsigned var, Occurrences &occurrences);
  void processITE(Formula* condition, Formula* thenBranch, Formula* elseBranch, Occurrences &occurrences);
  void processMatch(Term::SpecialTermData* sd, Term* term, Occurrences &occurrences);
  void processLet(Term::SpecialTermData* sd, TermList contents, Occurrences &occurrences);
  TermList eliminateLet(Term::SpecialTermData *sd, TermList contents);

  TermList nameLetBinding(unsigned symbol, VList *bindingVariables, TermList binding, TermList contents);
  TermList inlineLetBinding(unsigned symbol, VList *bindingVariables, TermList binding, TermList contents);

  TermList findITEs(TermList ts, Stack<unsigned> &variables, Stack<Formula*> &conditions,
                    Stack<TermList> &thenBranches, Stack<TermList> &elseBranches,
                    Stack<unsigned> &matchVariables, Stack<List<Formula*>*> &matchConditions,
                    Stack<List<TermList>*> &matchBranches);

  unsigned createFreshVariable(TermList sort);
  void createFreshVariableRenaming(unsigned oldVar, unsigned freshVar);

  bool shouldInlineITE(unsigned iteCounter);
}; // class NewCNF

}
#endif
