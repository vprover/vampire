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

typedef ApplicativeHelper AH;

/**
 * Initialise the term sharing structure.
 * @since 29/12/2007 Manchester
 */
TermSharing::TermSharing()
  : _poly(true),
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

  //combinatory superposiiton can introduce polymorphism into a monomorphic problem
  _poly = env.getMainProblem()->isHigherOrder() || env.getMainProblem()->hasPolymorphicSym() ||
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
      swap(ts1->_content, ts2->_content);
    }
  }

  Term* s = _terms.insert(t);
  if (s == t) {
    unsigned weight = 1;
    unsigned vars = 0;
    bool hasInterpretedConstants=t->arity()==0 &&
	env.signature->getFunction(t->functor())->interpreted();
    bool hasTermVar = false;
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
    
    unsigned typeArity = t->numTypeArguments();
    for (unsigned i = 0; i < t->arity(); i++) {
      TermList* tt = t->nthArgument(i);
      if (tt->isVar()) {
        ASS(tt->isOrdinaryVar());
        if(i >= typeArity){
          hasTermVar = true;
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
        hasTermVar |= r->hasTermVar();
        if (env.colorUsed) {
          color = static_cast<Color>(color | r->color());
        }
        if(!hasInterpretedConstants && r->hasInterpretedConstants()) {
          hasInterpretedConstants=true; 
        }
      }
    }
    t->markShared();
    t->setId(_terms.size());
    t->setNumVarOccs(vars);
    t->setWeight(weight);
    t->setHasTermVar(hasTermVar);
    if (env.colorUsed) {
      Color fcolor = env.signature->getFunction(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }

    t->setInterpretedConstantsPresence(hasInterpretedConstants);

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

  TIME_TRACE("sort sharing");

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
  
        vars += r->numVarOccs();
        weight += r->weight();
      }
    }
    sort->markShared();
    sort->setId(_sorts.size());
    sort->setNumVarOccs(vars);
    sort->setWeight(weight);

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
      swap(ts1->_content, ts2->_content);
    }
  }

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
    t->setId(_literals.size());
    t->setNumVarOccs(vars);
    t->setWeight(weight);
    if (env.colorUsed) {
      Color fcolor = env.signature->getPredicate(t->functor())->color();
      color = static_cast<Color>(color | fcolor);
      t->setColor(color);
    }
    t->setInterpretedConstantsPresence(hasInterpretedConstants);

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
    swap(ts1->_content, ts2->_content);
  }

  //we need these values set during insertion into the sharing set
  t->markTwoVarEquality();
  t->setTwoVarEqSort(sort);

  Literal* s = _literals.insert(t);
  if (s == t) {
    t->markShared();
    t->setId(_literals.size());
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
  }
  else {
    t->destroy();
  }
  return s;
} // TermSharing::insertVariableEquality

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
template<bool opposite>
bool TermSharing::equals(const Literal* l1, const Literal* l2)
{
  CALL("TermSharing::equals(Literal*,Literal*)");

  if( (l1->polarity()==l2->polarity()) == opposite) {
    return false;
  }

  if(l1->isTwoVarEquality() && l2->isTwoVarEquality() &&
      l1->twoVarEqSort()!=l2->twoVarEqSort()) {
    return false;
  }

  return equals(static_cast<const Term*>(l1), static_cast<const Term*>(l2));
}
