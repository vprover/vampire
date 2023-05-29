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
 * @file TermIterators.cpp
 * Implements several iteratorn over terms.
 */


#include "Debug/Tracer.hpp"

#include "Term.hpp"
#include "Signature.hpp"
#include "TermIterators.hpp"
#include "ApplicativeHelper.hpp"
#include "Lib/Deque.hpp"

namespace Kernel
{

/**
 * True if there exists next variable
 */
bool VariableIterator::hasNext()
{
  CALL("VariableIterator::hasNext");
  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used && _stack.top()->isVar()) {
    return true;
  }
  while(!_stack.isEmpty()) {
    const TermList* t=_stack.pop();
    if(_used && t->isVar()) {
      _used=false;
      t=t->next();
    }
    if(t->isEmpty()) {
	continue;
    }
    if(t->isVar()) {
      ASS(!_used);
      _stack.push(t);
      return true;
    }
    _stack.push(t->next());
    ASS(t->isTerm());
    const Term* trm=t->term();
    if(!trm->shared() || !trm->ground()) {
      _stack.push(trm->args());
    }
  }
  return false;
}

///////////////////////////////////////////

bool VariableWithSortIterator::hasNext()
{
  CALL("VariableWithSortIterator::hasNext");
  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used && _stack.top()->isVar()) {
    return true;
  }
  while(!_stack.isEmpty()) {
    const TermList* t=_stack.pop();
    if(_used && t->isVar()) {
      _used=false;
      _argNums.top()++;
      t=t->next();
    }
    if(t->isEmpty()) {
      _terms.pop();
      _argNums.pop();
	    continue;
    }
    if(t->isVar()) {
      ASS(!_used);
      _stack.push(t);
      return true;
    }
    _argNums.top()++;
    _stack.push(t->next());
    ASS(t->isTerm());
    const Term* trm=t->term();
    if(!trm->shared() || !trm->ground()) {
      _argNums.push(0);
      _terms.push(trm);
      _stack.push(trm->args());
    }
  }
  return false;
}

///////////////////////////////////////////


/**
 * True if there exists next subterm
 */
bool SubtermIterator::hasNext()
{
  CALL("SubtermIterator::hasNext");

  if(_stack->isEmpty()) {
    return false;
  }
  if(!_used) {
    return true;
  }
  _used=false;
  const TermList* t=_stack->pop();
  pushNext(t->next());
  if(t->isTerm()) {
    pushNext(t->term()->args());
  }
  return !_stack->isEmpty();
}

/**
 * Skip subterms of the term just returned by the @b next function
 *
 * Must be called after the @b next function before the @b hasNext
 * function is called again.
 */
void SubtermIterator::right()
{
  CALL("SubtermIterator::right");
  ASS(_stack->isNonEmpty());
  ASS(_used);

  _used=false;
  const TermList* t=_stack->pop();
  pushNext(t->next());

  //we did here the same as in the hasNext function, we only didn't call
  //the pushNext function on arguments of t
}


//////////////////////////////////////////////////////////////////////////
///                                                                    ///
///            ITERATORS REQUIRED FOR HIGHER-ORDER REASONING           ///
///                                                                    ///
//////////////////////////////////////////////////////////////////////////

/*bool TopLevelVarLikeTermIterator::hasNext()
{
  CALL("TopLevelVarLikeTermIterator::hasNext");

  static TermStack args;
  TermList head;
  
  if(_next){ return true; }
  while(!_stack.isEmpty()){
    Term* t = _stack.pop();
    ASS(t->isApplication());
    AH::getHeadAndArgs(t, head, args);
    ASS(args.size());
    if(head.isVar() && args.size()){
      _next = t;
    } else if(AH::isComb(head) && !AH::isUnderApplied(head, args.size()) && !t->ground()){
      _next = t;
    } else {
      while(!args.isEmpty()){
        TermList tl = args.pop();
        if(tl.isApplication() && !tl.term()->ground()){
          _stack.push(tl.term());
        }
      }
    }
    if(_next) { return true; }
  }
  return false;  
}

TopLevelVarIterator::TopLevelVarIterator(TermList t)
{
  if(t.isVar()){
    _next = t;
    return;
  }
  _next.makeEmpty();

  static TermStack args;
  args.reset();
  TermList head;

  AH::getHeadAndArgs(t, head, args);

  if(!t.term()->ground() && !head.isVar() && 
     (!AH::isComb(head) || AH::isUnderApplied(head, args.size()))){
    _stack.push(t);
  }  
}


bool TopLevelVarIterator::hasNext()
{
  CALL("TopLevelVarIterator::hasNext");

  static TermStack args;
  static TermStack args2;
  args.reset();
  args2.reset();
  TermList head;
  TermList head2;
  
  if(!_next.isEmpty()){ return true; }
  while(!_stack.isEmpty()){
    TermList t = _stack.pop();
    if(t.isVar()){
      _next = t;
    } else {
      AH::getHeadAndArgs(t, head, args);
      ASS(!head.isVar());
      while(!args.isEmpty()){
        TermList tl = args.pop();
        if(tl.isVar()){
          _stack.push(tl);
        } else if (!tl.term()->ground()) {
          AH::getHeadAndArgs(tl, head2, args2);
          if(!head2.isVar() && (!AH::isComb(head2) || AH::isUnderApplied(head2, args2.size())) ){
             _stack.push(tl);
          }
        }
      }
    }
    if(!_next.isEmpty()) { return true; }
  }
  return false;  

}*/

#if VHOL

typedef ApplicativeHelper AH;

Term* FirstOrderSubtermIt::next()
{
  CALL("FirstOrderSubtermIt::next");

  static TermStack args;
  _added = 0;
  TermList head;
  args.reset();
  Term* t = _stack.pop();
  if(!t->isLambdaTerm() || _goInsideLambdas){
    AH::getHeadAndArgs(t, head, args);
    if(!head.isLambdaTerm()){
      for(unsigned i = 0; i < args.size(); i++){
        // TODO logic below is wrong 
        // (not as complete as possible, but not unsound)
        // A term that contains loose indices may still
        // have subterms that don't have loose indices
        // Moreover, we do not explore the body of a lambda currently
        if(!args[i].isVar() && !args[i].containsLooseIndex()){
          // demodulating a term that contains a loose index
          // is sound, but it may not maintain completeness
          // depending on the ordering
          _added++;
          _stack.push(args[i].term());
        }
      }
    }
  }
  return t;
}

void FirstOrderSubtermIt::right()
{
  CALL("FirstOrderSubtermIt::right");

  while (_added > 0) {
    _added--;
    _stack.pop();
  }
} // FirstOrderSubtermIt::right

bool BooleanSubtermIt::hasNext()
{
  CALL("BooleanSubtermIt::hasNext");

  if(!_used){ return true; }

  static TermStack args;
  TermList head;
  while(!_stack.isEmpty()){
    Term* t = _stack.pop();
    if(t->isLambdaTerm()) {
      // Beware of the loose indices!
      // We could strengthen the iterator by returning subterms
      // underneath lambdas that don't contain loose indices
      continue;
    }
    AH::getHeadAndArgs(t, head, args);
    if(SortHelper::getResultSort(t).isBoolSort() && !AH::isBool(head)){
      _next = TermList(t);
      _used = false;
    }
    while(!args.isEmpty()){
      TermList arg = args.pop();
      if(arg.isTerm()){
        _stack.push(arg.term());
      }
    }
    if(!_used){ return true; }
  }
  return false;
}

#endif

//////////////////////////////////////////////////////////////////////////
///                                                                    ///
///                    END OF HIGHER-ORDER ITERATORS                   ///
///                                                                    ///
//////////////////////////////////////////////////////////////////////////

/**
 * True if there exists next subterm
 */
bool PolishSubtermIterator::hasNext()
{
  CALL("PolishSubtermIterator::hasNext");

  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used) {
    return true;
  }
  _used=false;
  const TermList* t=_stack.pop();
  pushNext(t->next());
  return !_stack.isEmpty();
}

//////////////////////////////////


/**
 * Return the next non-variable subterm.
 * @since 04/05/2013 Manchester
 * @author Andrei Voronkov
 */
TermList NonVariableIterator::next()
{
  CALL("NonVariableIterator::next");

  Term* t = _stack.pop();
  _added = 0;
  Term::Iterator ts(t);
  for (const TermList* ts = t->args();!ts->isEmpty();ts = ts->next()) {
    if (ts->isTerm()) {
      _stack.push(const_cast<Term*>(ts->term()));
      _added++;
    }
  }
  return TermList(t);
} // NonVariableIterator::next

/**
 * Skip all subterms of the terms returned by the last call to next()
 * @since 04/05/2013 Manchester
 * @author Andrei Voronkov
 */
void NonVariableIterator::right()
{
  CALL("NonVariableIterator::right");

  while (_added > 0) {
    _added--;
    _stack.pop();
  }
} // NonVariableIterator::right

/**
 * Return the next non-variable subterm that is not a type argument.
 * @since 20/06/2019 Manchester
 * @author Ahmed Bhayat
 */
Term* NonVariableNonTypeIterator::next()
{
  CALL("NonVariableNonTypeIterator::next");

  Term* t = _stack.pop();
  TermList* ts;
  _added = 0;  
  Signature::Symbol* sym;
  if (t->isLiteral()) {
    sym = env.signature->getPredicate(t->functor());
  } else{
    sym = env.signature->getFunction(t->functor());
  }
  unsigned taArity; 
  unsigned arity;

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()){
    taArity = 0;
    arity = 2;
  } else {
    taArity = sym->numTypeArguments();
    arity = sym->arity();
  }

  for(unsigned i = taArity; i < arity; i++){
    ts = t->nthArgument(i);
    if (ts->isTerm()) {
      _stack.push(const_cast<Term*>(ts->term()));
      _added++;
    }
  }
  return t;
}

/**
 * Skip all subterms of the terms returned by the last call to next()
 */
void NonVariableNonTypeIterator::right()
{
  CALL("NonVariableNonTypeIterator::right");

  while (_added > 0) {
    _added--;
    _stack.pop();
  }
} // NonVariableIterator::right

/**
 * True if there exists next non-variable subterm
 */
// bool NonVariableIterator::hasNext()
// {
//   CALL("NonVariableIterator::hasNext");

//   if(_stack.isEmpty()) {
//     return false;
//   }
//   ASS(_stack.top()->isTerm());
//   if(!_used) {
//     return true;
//   }
//   _used=false;
//   const TermList* t=_stack.pop();
//   pushNextNonVar(t->next());
//   pushNextNonVar(t->term()->args());
//   return !_stack.isEmpty();
// }

// /**
//  * Skip subterms of the term just returned by the @b next function
//  *
//  * Must be called after the @b next function before the @b hasNext
//  * function is called again.
//  */
// void NonVariableIterator::right()
// {
//   CALL("NonVariableIterator::right");
//   ASS(_stack.isNonEmpty());
//   ASS(_used);

//   _used=false;
//   const TermList* t=_stack.pop();
//   pushNextNonVar(t->next());

//   //we did here the same as in the hasNext function, we only didn't call
//   //the pushNextNonVar function on arguments of t
// }

// void NonVariableIterator::pushNextNonVar(const TermList* t)
// {
//   while(t->isVar()) {
//     t=t->next();
//   }
//   if(!t->isEmpty()) {
//     ASS(t->isTerm());
//     _stack.push(t);
//   }
// }


///////////////////////////////////////////

/**
 * True if there exists another disagreement between the two
 * terms specified in the constructor.
 */
bool DisagreementSetIterator::hasNext()
{
  CALL("DisagreementSetIterator::hasNext");
  ASS(_stack.size()%2==0);

  if(!_arg1.isEmpty()) {
    return true;
  }
  if(_stack.isEmpty()) {
    return false;
  }
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!_stack.isEmpty()) {
    tt=_stack.pop();
    ss=_stack.pop();
    if(!ss->next()->isEmpty()) {
      _stack.push(ss->next());
      _stack.push(tt->next());
    }
    if(!_disjunctVariables && ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      if(ss->term()->arity()) {
	_stack.push(ss->term()->args());
	_stack.push(tt->term()->args());
      }
    } else {
      _arg1=*ss;
      _arg2=*tt;
      return true;
    }
  }
  return false;
}


///////////////////////////////////////////

/**
 * Build an iterator over symbols of t.
 * @since 26/05/2007 Manchester
 */
TermFunIterator::TermFunIterator (const Term* t)
  : _stack(64)
{
  CALL("TermFunIterator::TermFunIterator");

  _hasNext = true;
  _next = t->functor();
  _stack.push(t->termArgs());
} // TermFunIterator::TermFunIterator


/**
 * True if there the next function.
 * @since 26/05/2007 Manchester
 */
bool TermFunIterator::hasNext ()
{
  CALL("TermFunIterator::hasNext");

  if (_hasNext) {
    return true;
  }

  while (_stack.isNonEmpty()) {
    const TermList* ts = _stack.pop();
    if (ts->isEmpty()) {
      continue;
    }
    _stack.push(ts->next());
    if (ts->isVar()) {
      continue;
    }
    _hasNext = true;
    const Term* t = ts->term();
    _next = t->functor();
    _stack.push(t->termArgs());
    return true;
  }
  return false;
} // TermFunIterator::hasNext


/**
 * Return the next symbol.
 * @since 26/05/2007 Manchester
 */
unsigned TermFunIterator::next ()
{
  CALL("TermFunIterator::hasNext");

  ASS(_hasNext);

  _hasNext = false;
  return _next;
} // TermFunIterator::next


///////////////////////////////////////////

/**
 * Build an iterator over variables of t.
 */
TermVarIterator::TermVarIterator (const Term* t)
  : _stack(64)
{
  CALL("TermVarIterator::TermVarIterator");
  //TODO update for two var lits?
  _stack.push(t->args());
} // TermVarIterator::TermVarIterator

/**
 * Build an iterator over variables of t.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented
 */
TermVarIterator::TermVarIterator (const TermList* ts)
  : _stack(64)
{
  CALL("TermVarIterator::TermVarIterator");
  _stack.push(ts);
} // TermVarIterator::TermVarIterator


/**
 * True if there the next variable.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for new datastructures
 */
bool TermVarIterator::hasNext ()
{
  CALL("TermVarIterator::hasNext");

  while (_stack.isNonEmpty()) {
    const TermList* ts = _stack.pop();
    if (ts->isEmpty()) {
      continue;
    }
    _stack.push(ts->next());
    if (ts->isVar()) {
      _next = ts->var();
      return true;
    }
    _stack.push(ts->term()->args());
  }
  return false;
} // TermVarIterator::hasNext


/**
 * Return the next variable.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for new datastructures
 */
unsigned TermVarIterator::next ()
{
  CALL("TermVarIterator::next");
  return _next;
} // TermVarIterator::next


///////////////////////////////////////////



}
