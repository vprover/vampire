/**
 * @file TermIterators.hpp
 * Defines several iteratorn over terms.
 */

#ifndef __TermIterators__
#define __TermIterators__

#include "Forwards.hpp"

#include "Lib/Recycler.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Term.hpp"


namespace Kernel {

/**
 * Iterator that yields variables of specified
 * @b term in DFS left to right order.
 */
class VariableIterator
: public IteratorCore<TermList>
{
public:
  DECL_ELEMENT_TYPE(TermList);
  VariableIterator(const Term* term) : _stack(8), _used(false)
  {
    if(!term->shared() || !term->ground()) {
      _stack.push(term->args());
    }
  }

  VariableIterator(TermList t) : _stack(8), _used(false)
  {
    if(t.isVar()) {
      _aux[0].makeEmpty();
      _aux[1]=t;
      _stack.push(&_aux[1]);
    }
    else {
      Term* term=t.term();
      if(!term->shared() || !term->ground()) {
	_stack.push(term->args());
      }
    }
  }

  bool hasNext();
  /** Return the next variable
   * @warning hasNext() must have been called before */
  TermList next()
  {
    ASS(!_used);
    ASS(_stack.top()->isVar());
    _used=true;
    return *_stack.top();
  }
private:
  Stack<const TermList*> _stack;
  bool _used;
  TermList _aux[2];
};


/**
 * Iterator that yields proper subterms
 * of @b term in DFS left to right order.
 */
class SubtermIterator
: public IteratorCore<TermList>
{
public:
  SubtermIterator(const Term* term) : _used(false)
  {
    Recycler::get(_stack);
    _stack->reset();

    pushNext(term->args());
  }
  ~SubtermIterator()
  {
    Recycler::release(_stack);
  }

  bool hasNext();
  /** Return next subterm
   * @warning hasNext() must have been called before */
  TermList next()
  {
    ASS(!_used && !_stack->isEmpty());
    _used=true;
    return *_stack->top();
  }

  void right();
protected:
  SubtermIterator() : _used(false)
  {
    Recycler::get(_stack);
    _stack->reset();
  }

  inline
  void pushNext(const TermList* t)
  {
    if(!t->isEmpty()) {
      _stack->push(t);
    }
  }

  Stack<const TermList*>* _stack;
  bool _used;
};

/**
 * Iterator that yields proper subterms of commutative
 * literal @b lit in DFS left to right order with the
 * arguments of the literal reversed.
 */
class ReversedCommutativeSubtermIterator
: public SubtermIterator
{
public:
  ReversedCommutativeSubtermIterator(const Term* trm)
  {
    CALL("Term::ReversedCommutativeSubtermIterator::ReversedCommutativeSubtermIterator");
    ASS(trm->commutative());
    ASS_EQ(trm->arity(),2);

    aux[0]=*trm->nthArgument(1);
    aux[1].makeEmpty();
    aux[2]=*trm->nthArgument(0);
    aux[3].makeEmpty();

    _stack->push(&aux[0]);
    _stack->push(&aux[2]);
  }
private:
  TermList aux[4];
};

/**
 * Iterator that yields proper subterms
 * of specified @b term, so that for each function it first yields
 * its arguments left to right, and then the function itself.
 */
class PolishSubtermIterator
: public IteratorCore<TermList>
{
public:
  PolishSubtermIterator(const Term* term) : _stack(8), _used(false)
  {
    pushNext(term->args());
  }

  bool hasNext();
  /** Return next subterm
   * @warning hasNext() must have been called before */
  TermList next()
  {
    ASS(!_used && !_stack.isEmpty());
    _used=true;
    return *_stack.top();
  }
private:
  inline
  void pushNext(const TermList* t)
  {
    while(!t->isEmpty()) {
      _stack.push(t);
      if(!t->isTerm()) {
	return;
      }
      t=t->term()->args();
    }
  }
  Stack<const TermList*> _stack;
  bool _used;
};

/**
 * Iterator that yields non-variable proper subterms
 * of specified @b term in DFS left to right order.
 */
class NonVariableIterator
: public IteratorCore<TermList>
{
public:
  NonVariableIterator(const Term* term) : _stack(8), _used(false)
  {
    pushNextNonVar(term->args());
  }

  bool hasNext();
  /** Return next non-variable subterm.
   * @warning hasNext() must have been called before */
  TermList next()
  {
    ASS(!_used && !_stack.top()->isVar());
    _used=true;
    return *_stack.top();
  }

  void right();
private:
  void pushNextNonVar(const TermList* t);

  Stack<const TermList*> _stack;
  bool _used;
};

/**
 * Iterator that iterator over disagreement set of two terms
 * or literals in DFS left to right order.
 */
class DisagreementSetIterator
: public IteratorCore<pair<TermList, TermList> >
{
public:
  DisagreementSetIterator(TermList t1, TermList t2, bool disjunctVariables=true)
  : _stack(8), _disjunctVariables(disjunctVariables)
  {
    CALL("Term::DisagreementSetIterator::DisagreementSetIterator(TermList...)");
    ASS(!t1.isEmpty());
    ASS(!t2.isEmpty());

    if(!TermList::sameTop(t1,t2)) {
      _arg1=t1;
      _arg2=t2;
      return;
    }
    _arg1.makeEmpty();
    if(t1.isTerm() && t1.term()->arity()>0) {
      _stack.push(t1.term()->args());
      _stack.push(t2.term()->args());
    }
  }
  /**
   * Create an iterator over the disagreement set of two terms/literals
   * with the same top functor
   */
  DisagreementSetIterator(Term* t1, Term* t2, bool disjunctVariables=true)
  : _stack(8), _disjunctVariables(disjunctVariables)
    {
    ASS_EQ(t1->functor(), t2->functor());
    _arg1.makeEmpty();

    if(t1->arity()>0) {
      _stack.push(t1->args());
      _stack.push(t2->args());
    }
  }

  bool hasNext();

  /** Return next subterm
   * @warning hasNext() must have been called before */
  pair<TermList, TermList> next()
  {
    pair<TermList, TermList> res(_arg1,_arg2);
    _arg1.makeEmpty();
    return res;
  }
private:
  Stack<TermList*> _stack;
  bool _disjunctVariables;
  TermList _arg1;
  TermList _arg2;
};



/**
 * Implements an iterator over function symbols of a term.
 *
 * Functions are yielded before their subterms.
 * @since 26/05/2007 Manchester, made from class TermVarIterator
 */
class TermFunIterator
: public IteratorCore<unsigned>
{
public:
  TermFunIterator (const Term*);

  bool hasNext();
  unsigned next();
private:
  /** True if the next symbol is found */
  bool _hasNext;
  /** next symbol, previously found */
  unsigned _next;
  /** Stack of term lists (not terms!) */
  Stack<const TermList*> _stack;
}; // class TermFunIterator


/**
 * Implements an iterator over variables of a term term list, or atom.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for different data structures
 */
class TermVarIterator
: public IteratorCore<unsigned>
{
public:
  TermVarIterator (const Term*);
  TermVarIterator (const TermList*);

  bool hasNext ();
  unsigned next ();
private:
  /** True if the next variable is found */
  bool _hasNext;
  /** next variable, previously found */
  unsigned _next;
  /** Stack of term lists (not terms!) */
  Stack<const TermList*> _stack;
}; // class TermVarIterator



}

#endif // __TermIterators__
