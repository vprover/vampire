/**
 * @file LPO.cpp
 * Implements class LPO for instances of the lexicographic ordering
 *
 */

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "LPO.hpp"
#include "Signature.hpp"

#define NONINTERPRETED_PRECEDENCE_BOOST 0x00001000
#define NONINTERPRETED_LEVEL_BOOST 0x00001000
#define COLORED_WEIGHT_BOOST 0x01000000
#define COLORED_LEVEL_BOOST 0x01000000
#define OMEGA 0x00010000

namespace Kernel {

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result LPO::compare(Literal* l1, Literal* l2) const
{
  CALL("LPO::compare(Literal*...)");
  ASS(l1->shared());
  ASS(l2->shared());

  if (l1 == l2) {
    return EQUAL;
  }

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if( (l1->isNegative() ^ l2->isNegative()) && (p1==p2) &&
	  l1->weight()==l2->weight() && l1->vars()==l2->vars() &&  //this line is just optimization, so we don't check whether literals are opposite when they cannot be
	  l1==env.sharing->tryGetOpposite(l2)) {
    return l1->isNegative() ? LESS : GREATER;
  }

  Result res;

  if (p1 != p2) {
    int prec1 = predicatePrecedence(p1);
    int prec2 = predicatePrecedence(p2);
    ASS_NEQ(prec1, prec2);
    if (prec1 > prec2) {
      res=GREATER;
      goto fin;
    }
    if (prec2 > prec1) {
      res=LESS;
      goto fin;
    }
  } else {
    if(l1->isEquality()) {
      ASS(l2->isEquality());
      return compareEqualities(l1, l2);
    }
    ASS(!l1->isEquality());

    /**/
    for (unsigned i=0; i < l1->arity(); i++) {
      Ordering::Result r = compare(*l1->nthArgument(i), *l2->nthArgument(i));
      if (r != EQUAL) {
        res=r;
        goto fin;
      }
    }
    res = INCOMPARABLE;
  }
  /**/

fin:
  if(_reverseLCM && (l1->isNegative() || l2->isNegative()) ) {
    if(l1->isNegative() && l2->isNegative()) {
      res = reverse(res);
    }
    else {
      res = l1->isNegative() ? LESS : GREATER;
    }
  }
  return res;
} // LPO::compare()

Ordering::Result LPO::compare(TermList tl1, TermList tl2) const
{
  CALL("LPO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }

  // LPO1
  if(tl1.isOrdinaryVar()) {
    return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
  }
  if(tl2.isOrdinaryVar()) {
    return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* s=tl1.term();
  Term* t=tl2.term();

  Ordering::Result r;
  bool tGTsi = true;
  bool sGTtj = true;
  
  for (unsigned i=0; i < t->arity(); i++) {
    r = compare(tl1, *t->nthArgument(i));
    if (r == EQUAL || r == LESS) {
      return LESS; // LPO2a
    } else if (r != GREATER) {
      sGTtj = false;
    }
  }

  for (unsigned i=0; i < s->arity(); i++) {
    r = compare(tl2, *s->nthArgument(i));
    if (r == EQUAL || r == LESS) {
      return GREATER; // LPO2a
    } else if (r != GREATER) {
      tGTsi = false;
    }
  }
  
  switch (compareFunctionPrecedences(s->functor(), t->functor())) {
  case EQUAL:
    // case LPO2c
    for (unsigned i=0; i < s->arity(); i++) {
      switch (compare(*s->nthArgument(i), *t->nthArgument(i))) {
      case EQUAL:
        continue;
      case INCOMPARABLE:
        return INCOMPARABLE;
      case LESS:
        return tGTsi ? LESS : INCOMPARABLE;
      case GREATER:
        return sGTtj ? GREATER : INCOMPARABLE;
      }
    }
    return EQUAL;
  case LESS:
    // case LPO2b
    return tGTsi ? LESS : INCOMPARABLE;
  case GREATER:
    // case LPO2b
    return sGTtj ? GREATER : INCOMPARABLE;
  default:
    ASSERTION_VIOLATION;
    return INCOMPARABLE;
  }
}

//////////////////////////////////////////////////
// LPOBase class
//////////////////////////////////////////////////

/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality). If a predicate is colored, its level is multiplied by
 * the COLORED_LEVEL_BOOST value.
 * @since 11/05/2008 Manchester
 */
int LPOBase::predicateLevel (unsigned pred) const
{
  int basic=pred >= _predicates ? 1 : _predicateLevels[pred];
  if(NONINTERPRETED_LEVEL_BOOST && !env.signature->getPredicate(pred)->interpreted()) {
    ASS_NEQ(pred,0); //equality is always interpreted
    basic+=NONINTERPRETED_LEVEL_BOOST;
  }
  if(env.signature->predicateColored(pred)) {
    ASS_NEQ(pred,0); //equality should never be colored
    return COLORED_LEVEL_BOOST*basic;
  } else {
    return basic;
  }
} // LPO::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 * @since 11/05/2008 Manchester
 */
int LPOBase::predicatePrecedence (unsigned pred) const
{
  int res=pred >= _predicates ? (int)pred : _predicatePrecedences[pred];
  if(NONINTERPRETED_PRECEDENCE_BOOST) {
    ASS_EQ(NONINTERPRETED_PRECEDENCE_BOOST & 1, 0); // an even number

    bool intp = env.signature->getPredicate(pred)->interpreted();
    res *= 2;
    return intp ? res+1 : res+NONINTERPRETED_PRECEDENCE_BOOST;
  }
  return res;
} // LPO::predicatePrecedences

Comparison LPOBase::compareFunctors(unsigned fun1, unsigned fun2) const
{
  CALL("LPOBase::compareFunctors");

  switch(compareFunctionPrecedences(fun1, fun2)) {
  case EQUAL: return Lib::EQUAL;
  case GREATER: return Lib::GREATER;
  case LESS: return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Compare precedences of two function symbols
 */
Ordering::Result LPOBase::compareFunctionPrecedences(unsigned fun1, unsigned fun2) const
{
  CALL("LPOBase::compareFunctionPrecedences");

  if (fun1 == fun2) {
    return EQUAL;
  }

  Signature::Symbol* s1=env.signature->getFunction(fun1);
  Signature::Symbol* s2=env.signature->getFunction(fun2);

  // term algebra constructor must be smaller than other symbols
  if (s1->termAlgebraCons() && !s2->termAlgebraCons()) {
    return LESS;
  }
  if (!s1->termAlgebraCons() && s2->termAlgebraCons()) {
    return GREATER;
  }
  
  if(!s1->interpreted()) {
    if(s2->interpreted()) {
      return GREATER;
    }
    //two non-interpreted functions
    return fromComparison(Int::compare(
        fun1 >= _functions ? (int)fun1 : _functionPrecedences[fun1],
        fun2 >= _functions ? (int)fun2 : _functionPrecedences[fun2] ));
  }
  if(!s2->interpreted()) {
    return LESS;
  }
  if(s1->arity()) {
    if(!s2->arity()) {
      return GREATER;
    }
    //two interpreted functions
    return fromComparison(Int::compare(fun1, fun2));
  }
  if(s2->arity()) {
    return LESS;
  }
  //two interpreted constants

  Comparison cmpRes;
  if(s1->integerConstant() && s2->integerConstant()) {
    cmpRes = IntegerConstantType::comparePrecedence(s1->integerValue(), s2->integerValue());
  }
  else if(s1->rationalConstant() && s2->rationalConstant()) {
    cmpRes = RationalConstantType::comparePrecedence(s1->rationalValue(), s2->rationalValue());
  }
  else if(s1->realConstant() && s2->realConstant()) {
    cmpRes = RealConstantType::comparePrecedence(s1->realValue(), s2->realValue());
  }
  else if(s1->integerConstant()) {
    ASS(s2->rationalConstant() || s2->realConstant());
    cmpRes = Lib::LESS;
  }
  else if(s2->integerConstant()) {
    ASS(s1->rationalConstant() || s1->realConstant());
    cmpRes = Lib::GREATER;
  }
  else if(s1->rationalConstant()) {
    ASS(s2->realConstant());
    cmpRes = Lib::LESS;
  }
  else if(s2->rationalConstant()) {
    ASS(s1->realConstant());
    cmpRes = Lib::GREATER;
  }
  else {
    ASSERTION_VIOLATION;
    cmpRes = Int::compare(fun1, fun2);
  }
  return fromComparison(cmpRes);
}

struct FnArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u1),
	    env.signature->functionArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u1),
	    env.signature->predicateArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

struct FnRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u2),
	    env.signature->functionArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u2),
	    env.signature->predicateArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};


/**
 * Create a LPOBase object.
 */
LPOBase::LPOBase(Problem& prb, const Options& opt)
  : _predicates(env.signature->predicates()),
    _functions(env.signature->functions()),
    _predicateLevels(_predicates),
    _predicatePrecedences(_predicates),
    _functionPrecedences(_functions)
{
  CALL("LPOBase::LPOBase");
  ASS_G(_predicates, 0);

  DArray<unsigned> aux(32);
  if(_functions) {
    aux.initFromIterator(getRangeIterator(0u, _functions), _functions);

    switch(opt.symbolPrecedence()) {
    case Shell::Options::SymbolPrecedence::ARITY:
      aux.sort(FnArityComparator());
      break;
    case Shell::Options::SymbolPrecedence::REVERSE_ARITY:
      aux.sort(FnRevArityComparator());
      break;
    case Shell::Options::SymbolPrecedence::OCCURRENCE:
      break;
    }

    for(unsigned i=0;i<_functions;i++) {
      _functionPrecedences[aux[i]]=i;
    }
  }

  aux.initFromIterator(getRangeIterator(0u, _predicates), _predicates);

  switch(opt.symbolPrecedence()) {
  case Shell::Options::SymbolPrecedence::ARITY:
    aux.sort(PredArityComparator());
    break;
  case Shell::Options::SymbolPrecedence::REVERSE_ARITY:
    aux.sort(PredRevArityComparator());
    break;
  case Shell::Options::SymbolPrecedence::OCCURRENCE:
    break;
  }
  for(unsigned i=0;i<_predicates;i++) {
    _predicatePrecedences[aux[i]]=i;
  }

  switch(opt.literalComparisonMode()) {
  case Shell::Options::LiteralComparisonMode::STANDARD:
    _predicateLevels.init(_predicates, 1);
    break;
  case Shell::Options::LiteralComparisonMode::PREDICATE:
  case Shell::Options::LiteralComparisonMode::REVERSE:
    for(unsigned i=1;i<_predicates;i++) {
      _predicateLevels[i]=_predicatePrecedences[i]+1;
    }
    break;
  }
  //equality is on the lowest level
  _predicateLevels[0]=0;

  _reverseLCM = opt.literalComparisonMode()==Shell::Options::LiteralComparisonMode::REVERSE;

  for(unsigned i=1;i<_predicates;i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    //consequence-finding name predicates have the lowest level
    if(predSym->label()) {
      _predicateLevels[i]=-1;
    }
    else if(predSym->equalityProxy()) {
      //equality proxy predicates have the highest level (lower than colored predicates)
      _predicateLevels[i]=_predicates+2;
    }

  }
}


}
