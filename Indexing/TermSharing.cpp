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
 * @file TermSharing.cpp
 * Implements class TermSharing.
 *
 * @since 28/12/2007 Manchester
 */

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"

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
    _totalSorts(0),
    // _groundTerms(0), //MS: unused
    _totalLiterals(0),
    // _groundLiterals(0), //MS: unused
    _literalInsertions(0),
    _sortInsertions(0),
    _termInsertions(0),
    _poly(1),
    _wellSortednessCheckingDisabled(false)
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
  Set<AtomicSort*,TermSharing>::Iterator ss(_sorts);
  while (ss.hasNext()) {
    ss.next()->destroy();
  }
#endif
}

void TermSharing::setPoly()
{
  CALL("TermSharing::setPoly()");

  //combinatory superposiiton can introduce polymorphism into a 
  //monomorphic problem
  _poly = env.property->higherOrder() ||
          env.property->hasPolymorphicSym() ||
          env.options->equalityProxy() != Options::EqualityProxy::OFF ||
          env.options->saturationAlgorithm() == Options::SaturationAlgorithm::INST_GEN;
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
  ASS(!t->isSort());

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

    if(env.options->combinatorySup()){ 
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
    t->setId(_totalTerms);
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      Color fcolor = env.signature->getFunction(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }
      
    t->setInterpretedConstantsPresence(hasInterpretedConstants);
    _totalTerms++;

    //poly function works for mono as well, but is slow
    //it is fine to use for debug
    ASS_REP(_wellSortednessCheckingDisabled || SortHelper::areImmediateSortsValidPoly(t), t->toString());
    if (!_poly && !SortHelper::areImmediateSortsValidMono(t) && !_wellSortednessCheckingDisabled){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");
    } else if (_poly && !SortHelper::areImmediateSortsValidPoly(t) && !_wellSortednessCheckingDisabled){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");      
    }
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insert

AtomicSort* TermSharing::insert(AtomicSort* sort)
{
  CALL("TermSharing::insert(AtomicSort*)");
  ASS(!sort->isLiteral());
  ASS(!sort->isSpecial());
  ASS(sort->isSort());

  // cannot use TC_TERM_SHARING
  // as inserting a term can result in the insertion of
  // a sort and TimeCounter design forbids starting a timer 
  // when it is alreadt running 
  TimeCounter tc(TC_SORT_SHARING);

  _sortInsertions++;
  AtomicSort* s = _sorts.insert(sort);
  if (s == sort) {
    if(sort->isArraySort()){
      _arraySorts.insert(TermList(sort));
    }    
    unsigned weight = 1;
    unsigned vars = 0;

    for (TermList* tt = sort->args(); ! tt->isEmpty(); tt = tt->next()) {
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
      }
    }
    sort->markShared();
    sort->setId(_totalSorts);
    sort->setVars(vars);
    sort->setWeight(weight);
      
    _totalSorts++;

    ASS_REP(SortHelper::allTopLevelArgsAreSorts(sort), sort->toString());
    if (!SortHelper::allTopLevelArgsAreSorts(sort)){
      USER_ERROR("Immediate subterms of sort "+sort->toString()+" are not all sorts as mandated in rank-1 polymorphism!");      
    }
  }
  else {
    sort->destroy();
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
  ASS(!t->isSort());
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
    t->setId(_totalLiterals);
    t->setVars(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      Color fcolor = env.signature->getPredicate(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }
    t->setInterpretedConstantsPresence(hasInterpretedConstants);
    _totalLiterals++;

     ASS_REP(_wellSortednessCheckingDisabled || SortHelper::areImmediateSortsValidPoly(t), t->toString());
    if (!_poly && !SortHelper::areImmediateSortsValidMono(t) && !_wellSortednessCheckingDisabled){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");
    } else if (_poly && !SortHelper::areImmediateSortsValidPoly(t) && !_wellSortednessCheckingDisabled){
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
    t->setId(_totalLiterals);
    t->setWeight(2 + sort.weight());
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

  // if both shared, we can just use ids (can they ever be non-shared here?)
  ASS_REP(trm1->shared(), trm1->toString());
  ASS_REP(trm2->shared(), trm2->toString());

  return (trm1->getId() > trm2->getId());
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


