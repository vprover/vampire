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
#include "Debug/TimeProfiling.hpp"

#include "TermSharing.hpp"

using namespace Kernel;
using namespace Indexing;

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

  _poly = 
#if VHOL
    env.property->higherOrder() || 
#endif
    env.property->hasPolymorphicSym() ||
    (env.options->equalityProxy() != Options::EqualityProxy::OFF && !env.options->useMonoEqualityProxy());
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

  TIME_TRACE(TimeTrace::TERM_SHARING);

  // normalise commutative terms
  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      t->argSwap();
    }
  }

#if VHOL

#endif

  _termInsertions++;
  Term* s = _terms.insert(t);
   if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    bool hasSortVar = false;
    bool hasInterpretedConstants=t->arity()==0 && 
         env.signature->getFunction(t->functor())->interpreted();
#if VHOL
    bool hasDBIndex = t->deBruijnIndex().isSome();
    bool hasRedex = t->isRedex();
    bool hasLambda = t->isLambdaTerm();
#endif
    Color color = COLOR_TRANSPARENT;
    
    unsigned typeArity = t->numTypeArguments();
    for (unsigned i = 0; i < t->arity(); i++) {
      TermList* tt = t->nthArgument(i);
      if (tt->isVar()) {
        ASS(tt->isOrdinaryVar());
        if(i < typeArity){
          hasSortVar = true;
        }
        vars++;
        weight += 1;
      }
      else 
      {
        ASS_REP(tt->term()->shared(), tt->term()->toString());
        
        Term* r = tt->term();
  
        vars += r->numVarOccs();
        weight += r->weight();
        hasSortVar |= r->hasSortVar();
#if VHOL                
        hasDBIndex              = hasDBIndex              ? true : r->hasDBIndex();
        hasRedex                = hasRedex                ? true : r->hasRedex();
        hasLambda               = hasLambda               ? true : r->hasLambda();
#endif
        hasInterpretedConstants = hasInterpretedConstants ? true : r->hasInterpretedConstants();
        if (env.colorUsed) {
          color = static_cast<Color>(color | r->color());
        }
      }
    }
    t->markShared();
    t->setId(_totalTerms);
    t->setNumVarOccs(vars);
    t->setWeight(weight);
    t->setHasSortVar(hasSortVar);

    if (env.colorUsed) {
      Color fcolor = env.signature->getFunction(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }

#if VHOL
    t->setHasRedex(hasRedex);
    t->setHasDBIndex(hasDBIndex);
    t->setHasLambda(hasLambda);
#endif      
    t->setInterpretedConstantsPresence(hasInterpretedConstants);
    _totalTerms++;

    //poly function works for mono as well, but is slow
    //it is fine to use for debug
    ASS_REP(_wellSortednessCheckingDisabled || SortHelper::areImmediateSortsValidPoly(t), t->toString());
    if (!_wellSortednessCheckingDisabled && !_poly && !SortHelper::areImmediateSortsValidMono(t)){
      USER_ERROR("Immediate (shared) subterms of  term/literal "+t->toString()+" have different types/not well-typed!");
    } else if (!_wellSortednessCheckingDisabled && _poly && !SortHelper::areImmediateSortsValidPoly(t)){
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

  TIME_TRACE("sort sharing");

  _sortInsertions++;
  AtomicSort* s = _sorts.insert(sort);
  if (s == sort) {
    if(sort->isArraySort()){
      _arraySorts.insert(TermList(sort));
    }    
    unsigned weight = 1;
    unsigned vars = 0;
    bool hasSortVar = false;

    for (TermList* tt = sort->args(); ! tt->isEmpty(); tt = tt->next()) {
      if (tt->isVar()) {
        ASS(tt->isOrdinaryVar());
        hasSortVar = true;
        vars++;
        weight += 1;
      }
      else 
      {
        ASS_REP(tt->term()->shared(), tt->term()->toString());
        
        Term* r = tt->term();
  
        vars += r->numVarOccs();
        weight += r->weight();
        hasSortVar |= r->hasSortVar();        
      }
    }
    sort->markShared();
    sort->setId(_totalSorts);
    sort->setNumVarOccs(vars);
    sort->setWeight(weight);
    sort->setHasSortVar(hasSortVar);
      
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

  TIME_TRACE(TimeTrace::TERM_SHARING);

  if (t->commutative()) {
    ASS(t->arity() == 2);

    TermList* ts1 = t->args();
    TermList* ts2 = ts1->next();
    if (argNormGt(*ts1, *ts2)) {
      t->argSwap();
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
        vars += r->numVarOccs();
        weight += r->weight();

        if(t->isEquality()){
          TermList sort = SortHelper::getResultSort(r);
          weight += sort.weight() - 1;
        }

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
    t->setNumVarOccs(vars);
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

  TIME_TRACE(TimeTrace::TERM_SHARING);

  TermList* ts1 = t->args();
  TermList* ts2 = ts1->next();
  if (argNormGt(*ts1, *ts2)) {
    t->argSwap();
  }

  //we need these values set during insertion into the sharing set
  t->markTwoVarEquality();
  t->setTwoVarEqSort(sort);

  _literalInsertions++;
  Literal* s = _literals.insert(t);
  if (s == t) {
    t->markShared();
    t->setId(_totalLiterals);
    // 3 since we have two variables and the equality symbol itself.
    // Additionally, we need sort.weight() in the polymorphic case since
    // the sort may contain variables and Vampire assumes the invariant
    // weight(lit) >= distinct_vars(lit)
    // The -1 factor is there not to make the overall weight different,
    // for the monomorpic case, than it was in the olden days
    // (which was 3 and sort.weight() is in such cases 1)
    // Note that this is not perfect with arrays, who's complex (ground) sort weighs more than 1
    // However, we don't want the calculation to depend on _poly
    // which switches from 1 to possibly 0 only after preprocessing.
    t->setWeight(3 + (sort.weight() - 1));
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

  TIME_TRACE(TimeTrace::TERM_SHARING);

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
    if (*ss != *tt) {
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


