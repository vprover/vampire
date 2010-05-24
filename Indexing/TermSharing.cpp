/**
 * @file TermSharing.cpp
 * Implements class TermSharing.
 *
 * @since 28/12/2007 Manchester
 */

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "TermSharing.hpp"


using namespace Kernel;
using namespace Indexing;

/**
 * Initialise the term sharing structure.
 * @since 29/12/2007 Manchester
 */
TermSharing::TermSharing()
  : _totalTerms(0),
    _groundTerms(0),
    _totalLiterals(0),
    _groundLiterals(0),
    _literalInsertions(0),
    _termInsertions(0)
{
}

/**
 * Destroy the term sharing structure.
 * @since 29/12/2007 Manchester
 */
TermSharing::~TermSharing()
{
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
  ASS(! t->isLiteral());

  TimeCounter tc(TC_TERM_SHARING);

  // normalise commutative terms
  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      size_t c = ts1->_content;
      ts1->_content = ts2->_content;
      ts2->_content = c;
    }
  }

  _termInsertions++;
  Term* s = _terms.insert(t);
  string n = "";
  if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    Color color = COLOR_TRANSPARENT;
    for (TermList* tt = t->args(); ! tt->isEmpty(); tt = tt->next()) {
      if (tt->isVar()) {
	ASS(tt->isOrdinaryVar());
	vars++;
	weight += 1;
      }
      else {
	ASS(tt->term()->shared());

	Term* r = tt->term();
	vars += r->vars();
	weight += r->weight();
	if (env.colorUsed) {
	  ASS(color == COLOR_TRANSPARENT || r->color() == COLOR_TRANSPARENT || color == r->color());
	  color = static_cast<Color>(color | r->color());
	}
      }
    }
    t->markShared();
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      if (color == COLOR_TRANSPARENT) {
	color = env.signature->getFunction(t->functor())->color();
      }
#if VDEBUG
      else {
	Color fcolor = env.signature->getFunction(t->functor())->color();
	ASS(! fcolor || color == fcolor);
      }
#endif
      t->setColor(color);
    }
    _totalTerms++;
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
Literal* TermSharing::insert(Literal* t)
{
  CALL("TermSharing::insert(Literal*)");
  ASS(t->isLiteral());

  TimeCounter tc(TC_TERM_SHARING);

  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      size_t c = ts1->_content;
      ts1->_content = ts2->_content;
      ts2->_content = c;
    }
  }

  _literalInsertions++;
  Literal* s = _literals.insert(t);
  string n = "";
  if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    Color color = COLOR_TRANSPARENT;
    for (TermList* tt = t->args(); ! tt->isEmpty(); tt = tt->next()) {
      if (tt->isVar()) {
	ASS(tt->isOrdinaryVar());
	vars++;
	weight += 1;
      }
      else {
	ASS(tt->term()->shared());
	Term* r = tt->term();
	vars += r->vars();
	weight += r->weight();
	if (env.colorUsed) {
	  ASS(color == COLOR_TRANSPARENT || r->color() == COLOR_TRANSPARENT || color == r->color());
	  color = static_cast<Color>(color | r->color());
	}
      }
    }
    t->markShared();
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      if (color == COLOR_TRANSPARENT) {
	color = env.signature->getPredicate(t->functor())->color();
      }
#if VDEBUG
      else {
	Color fcolor = env.signature->getPredicate(t->functor())->color();
	ASS(! fcolor || color == fcolor);
      }
#endif
      t->setColor(color);
    }
    _totalLiterals++;
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insert

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
  Literal* res;
  if(_literals.find(OpLitWrapper(l), res)) {
    return res;
  }
  return 0;
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
  //we did all we could to compare the two terms deterministicaly
  //(and efficiently), but they're too alike, so that we have to
  //compare their addresses to distinguish between them.
  return t1.content()>t2.content();

  //To avoid non-determinism, now we'll compare the terms lexicographicaly.
  //This could be slow, so it's good just for debugging purposes.
//  Term::SubtermIterator sit1(trm1);
//  Term::SubtermIterator sit2(trm2);
//  while(sit1.hasNext()) {
//    ALWAYS(sit2.hasNext());
//    TermList st1=sit1.next();
//    TermList st2=sit2.next();
//    if(st1.isTerm()) {
//	if(st2.isTerm()) {
//	  unsigned f1=st1.term()->functor();
//	  unsigned f2=st2.term()->functor();
//	  if(f1!=f2) {
//	    return f1>f2;
//	  }
//	} else {
//	  return true;
//	}
//    } else {
//	if(st2.isTerm()) {
//	  return false;
//	} else {
//	  if(st1.var()!=st2.var()) {
//	    return st1.var()>st2.var();
//	  }
//	}
//    }
//  }
//  ASS(trm1==trm2);
//  return false;
}


/**
 * True if the the top-levels of @b s and @b t are equal.
 * Used for inserting terms in a hash table.
 * @pre s and t must be non-variable terms
 * @since 28/12/2007 Manchester
 */
bool TermSharing::equals(const Term* s,const Term* t)
{
  CALL("TermSharing::equals");

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
