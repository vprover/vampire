
/*
 * File TermSharing.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TermSharing.cpp
 * Implements class TermSharing.
 *
 * @since 28/12/2007 Manchester
 */

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "TermSharing.hpp"

using namespace Kernel;
using namespace Indexing;

typedef ApplicativeHelper AH;

/**
 * Initialise the term sharing structure.
 * @since 29/12/2007 Manchester
 */
TermSharing::TermSharing()
  : _totalTerms(0),
    // _groundTerms(0), //MS: unused
    _totalLiterals(0),
    // _groundLiterals(0), //MS: unused
    _literalInsertions(0),
    _termInsertions(0)
{
  CALL("TermSharing::TermSharing");
}

/**
 * Destroy the term sharing structure.
 * @since 29/12/2007 Manchester
 */
TermSharing::~TermSharing()
{
  CALL("TermSharing::~TermSharing");

#if CHECK_LEAKS
  Set<Term*,TermSharing>::Iterator ts(_terms);
  while (ts.hasNext()) {
    ts.next()->destroy();
  }
  Set<Literal*,TermSharing>::Iterator ls(_literals);
  while (ls.hasNext()) {
    ls.next()->destroy();
  }
#endif
}

/**
 * Insert a new term in the index and return the result.
 * @since 28/12/2007 Manchester
 */
Term* TermSharing::insert(Term* t)
{

  CALL("TermSharing::insert(Term*)");
  ASS(!t->isLiteral());
  ASS(!t->isSpecial());

  TimeCounter tc(TC_TERM_SHARING);

  // normalise commutative terms
  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      swap(ts1->_content, ts2->_content);
    }
  }

  _termInsertions++;
  Term* s = _terms.insert(t);
   if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    bool hasInterpretedConstants=t->arity()==0 &&
	env.signature->getFunction(t->functor())->interpreted();
    Color color = COLOR_TRANSPARENT;
    if(env.options->combinatorySup() && !AH::isType(t)){ 
      int maxRedLength = -1;
      TermList head;
      TermStack args;
      AH::getHeadAndArgs(t, head, args);
      if(!AH::isComb(head) || AH::isUnderApplied(head, args.size())){
        maxRedLength = sumRedLengths(args);
      } else {
        switch(AH::getComb(head)){
          case Signature::B_COMB:
            if(!AH::isComb(AH::getHead(args[args.size()-1]))  &&
               !AH::isComb(AH::getHead(args[args.size()-2]))){
              maxRedLength = sumRedLengths(args);
              maxRedLength = maxRedLength == -1 ? -1 : maxRedLength + 1;
            }
            break;
          case Signature::S_COMB:
            if(!AH::isComb(AH::getHead(args[args.size()-1]))  &&
               !AH::isComb(AH::getHead(args[args.size()-2]))){
              maxRedLength = sumRedLengths(args);
              maxRedLength = maxRedLength == -1 ? -1 : maxRedLength + 1;
              if(maxRedLength != -1 && args[args.size() - 3].isTerm()){
                maxRedLength += args[args.size() - 3].term()->maxRedLength();
              }
            }
            break;
          case Signature::C_COMB:
          case Signature::I_COMB:
          case Signature::K_COMB:
            if(!AH::isComb(AH::getHead(args[args.size()-1]))){
              maxRedLength = sumRedLengths(args);
              maxRedLength = maxRedLength == -1 ? -1 : maxRedLength + 1;
            }
            break;
          default:
            ASSERTION_VIOLATION;
        }
      }
      t->setMaxRedLen(maxRedLength);
    }
    for (TermList* tt = t->args(); ! tt->isEmpty(); tt = tt->next()) {
      if (tt->isVar()) {
        ASS(tt->isOrdinaryVar());
        vars++;
        weight += 1;
      }
      else 
      {
        ASS_REP(tt->term()->shared(), tt->term()->toString());
        
        Term* r = tt->term();
  
        vars += r->vars();
        weight += r->weight();
        if (env.colorUsed) {
            color = static_cast<Color>(color | r->color());
        }
        if(!hasInterpretedConstants && r->hasInterpretedConstants()) {
            hasInterpretedConstants=true; 
        }
      }
    }
    t->markShared();
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      Color fcolor = env.signature->getFunction(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }
      
    t->setInterpretedConstantsPresence(hasInterpretedConstants);
    _totalTerms++;
     
    ASS_REP(SortHelper::areImmediateSortsValid(t), t->toString());
    if (!SortHelper::areImmediateSortsValid(t)){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");
    }
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insert

/**
 * Insert a new literal in the index and return the result.
 *
 * Equalities between two variables cannot be inserted using this
 * function. @c insertVariableEquality() must be used instead.
 *
 * @since 28/12/2007 Manchester
 */
Literal* TermSharing::insert(Literal* t)
{
  CALL("TermSharing::insert(Literal*)");
  ASS(t->isLiteral());
  ASS(!t->isSpecial());

  //equalities between variables must be inserted using insertVariableEquality() function
  ASS_REP(!t->isEquality() || !t->nthArgument(0)->isVar() || !t->nthArgument(1)->isVar(), t->toString());

  TimeCounter tc(TC_TERM_SHARING);

  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      swap(ts1->_content, ts2->_content);
    }
  }

  _literalInsertions++;
  Literal* s = _literals.insert(t);
  if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    Color color = COLOR_TRANSPARENT;
    bool hasInterpretedConstants=false;
    for (TermList* tt = t->args(); ! tt->isEmpty(); tt = tt->next()) {
      if (tt->isVar()) {
	ASS(tt->isOrdinaryVar());
	vars++;
	weight += 1;
      }
      else {
	ASS_REP(tt->term()->shared(), tt->term()->toString());
	Term* r = tt->term();
	vars += r->vars();
	weight += r->weight();
	if (env.colorUsed) {
	  ASS(color == COLOR_TRANSPARENT || r->color() == COLOR_TRANSPARENT || color == r->color());
	  color = static_cast<Color>(color | r->color());
	}
	if(!hasInterpretedConstants && r->hasInterpretedConstants()) {
	  hasInterpretedConstants=true;
	}
      }
    }
    t->markShared();
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      Color fcolor = env.signature->getPredicate(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }
    t->setInterpretedConstantsPresence(hasInterpretedConstants);
    _totalLiterals++;

    ASS_REP(SortHelper::areImmediateSortsValid(t), t->toString());
    if (!SortHelper::areImmediateSortsValid(t)){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");
    }
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insert

/**
 * Insert a new literal in the index and return the result.
 * @since 28/12/2007 Manchester
 */
Literal* TermSharing::insertVariableEquality(Literal* t, TermList sort)
{
  CALL("TermSharing::insertVariableEquality");
  ASS(t->isLiteral());
  ASS(t->commutative());
  ASS(t->isEquality());
  ASS(t->nthArgument(0)->isVar());
  ASS(t->nthArgument(1)->isVar());
  ASS(!t->isSpecial());

  TimeCounter tc(TC_TERM_SHARING);

  TermList* ts1 = t->args();
  TermList* ts2 = ts1->next();
  if (argNormGt(*ts1, *ts2)) {
    swap(ts1->_content, ts2->_content);
  }

  //we need these values set during insertion into the sharing set
  t->markTwoVarEquality();
  t->setTwoVarEqSort(sort);

  _literalInsertions++;
  Literal* s = _literals.insert(t);
  if (s == t) {
    t->markShared();
    t->setWeight(3);
    if (env.colorUsed) {
      t->setColor(COLOR_TRANSPARENT);
    }
    t->setInterpretedConstantsPresence(false);
    _totalLiterals++;
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insertVariableEquality

/**
 * Insert a new term and all its unshared subterms
 * in the index, and return the result.
 */
Term* TermSharing::insertRecurrently(Term* t)
{
  CALL("TermSharing::insert");

  TimeCounter tc(TC_TERM_SHARING);

  TermList tRef;
  tRef.setTerm(t);

  TermList* ts=&tRef;
  static Stack<TermList*> stack(4);
  static Stack<TermList*> insertingStack(8);
  for(;;) {
    if(ts->isTerm() && !ts->term()->shared()) {
      stack.push(ts->term()->args());
      insertingStack.push(ts);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
  }
  while(!insertingStack.isEmpty()) {
    ts=insertingStack.pop();
    ts->setTerm(insert(ts->term()));
  }
  return tRef.term();
}

/**
 * If the sharing structure contains a literal opposite to @b l, return it.
 * Otherwise return 0.
 */
Literal* TermSharing::tryGetOpposite(Literal* l)
{
  CALL("TermSharing::tryGetOpposite");

  Literal* res;
  if(_literals.find(OpLitWrapper(l), res)) {
    return res;
  }
  return 0;
}


int TermSharing::sumRedLengths(TermStack& args)
{
  CALL("TermSharing::sumRedLengths");

  int redLength = 0;

  for(unsigned i = 0; i < args.size(); i++){
    if(args[i].isTerm() && args[i].term()->maxRedLength() != -1){
      redLength += args[i].term()->maxRedLength();
    } else if(args[i].isTerm()) {
      return -1;
    }
  }
  return redLength;
}

/**
 * Return true if t1 is greater than t2 in some arbitrary
 * total ordering.
 *
 * Is used just for normalization of commutative term and
 * literal arguments.
 */
bool TermSharing::argNormGt(TermList t1, TermList t2)
{
  CALL("TermSharing::argNormGt");

  if(t1.tag()!=t2.tag()) {
    return t1.tag()>t2.tag();
  }
  if(!t1.isTerm()) {
    return t1.content()>t2.content();
  }
  Term* trm1=t1.term();
  Term* trm2=t2.term();
  if(trm1->functor()!=trm2->functor()) {
    return trm1->functor()>trm2->functor();
  }
  if(trm1->weight()!=trm2->weight()) {
    return trm1->weight()>trm2->weight();
  }
  if(trm1->vars()!=trm2->vars()) {
    return trm1->vars()>trm2->vars();
  }
//  //we did all we could to compare the two terms deterministicaly
//  //(and efficiently), but they're too alike, so that we have to
//  //compare their addresses to distinguish between them.
//  return t1.content()>t2.content();

  //To avoid non-determinism, now we'll compare the terms lexicographicaly.
  static DisagreementSetIterator dsit;
  dsit.reset(trm1, trm2, false);

  if(!dsit.hasNext()) {
    ASS_EQ(trm1,trm2);
    return false;
  }

  pair<TermList, TermList> diff=dsit.next();
  TermList st1=diff.first;
  TermList st2=diff.second;
  if(st1.isTerm()) {
    if(st2.isTerm()) {
      unsigned f1=st1.term()->functor();
      unsigned f2=st2.term()->functor();
      ASS_NEQ(f1,f2);
      return f1>f2;
    } else {
      return true;
    }
  } else {
    if(st2.isTerm()) {
      return false;
    } else {
      ASS_NEQ(st1.var(),st2.var());
      return st1.var()>st2.var();
    }
  }
  ASSERTION_VIOLATION;
  return false;
}


/**
 * True if the the top-levels of @b s and @b t are equal.
 * Used for inserting terms in a hash table.
 * @pre s and t must be non-variable terms
 * @since 28/12/2007 Manchester
 */
bool TermSharing::equals(const Term* s,const Term* t)
{
  CALL("TermSharing::equals(Term*,Term*)");

  if (s->functor() != t->functor()) return false;

  const TermList* ss = s->args();
  const TermList* tt = t->args();
  while (! ss->isEmpty()) {
    if (ss->_content != tt->_content) {
      return false;
    }
    ss = ss->next();
    tt = tt->next();
  }
  return true;
} // TermSharing::equals

/**
 * True if the two literals are equal (or equal except polarity if @c opposite is true)
 */
bool TermSharing::equals(const Literal* l1, const Literal* l2, bool opposite)
{
  CALL("TermSharing::equals(Literal*,Literal*)");

  if( (l1->polarity()==l2->polarity()) == opposite) {
    return false;
  }

  if(l1->isTwoVarEquality() && l2->isTwoVarEquality() &&
      l1->twoVarEqSort()!=l2->twoVarEqSort()) {
    return false;
  }

  return equals(static_cast<const Term*>(l1),
		static_cast<const Term*>(l2));
}


