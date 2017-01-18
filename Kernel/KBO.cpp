/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
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
#include "KBO.hpp"
#include "Signature.hpp"


#define NONINTERPRETED_PRECEDENCE_BOOST 0x1000

#define NONINTERPRETED_LEVEL_BOOST 0x1000
#define COLORED_WEIGHT_BOOST 0x10000
#define COLORED_LEVEL_BOOST 0x10000

namespace Kernel {

using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO* kbo)
    : _kbo(*kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  CLASS_NAME(KBO::State);
  USE_ALLOCATOR(State);

  void traverse(Term* t1, Term* t2);
  void traverse(TermList tl,int coefficient);
  Result result(Term* t1, Term* t2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList t1, TermList t2);
  Result applyVariableCondition(Result res)
  {
    if(_posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(_negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int _weightDiff;
  DHMap<unsigned, int, IdentityHash> _varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int _posNum;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result KBO::State::result(Term* t1, Term* t2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    if(t1->isLiteral()) {
      int prec1, prec2;
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else {
      res=_kbo.compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

  //the result should never be EQUAL:
  //- either t1 and t2 are truely equal. But then if they're equal, it
  //would have been discovered by the t1==t2 check in
  //KBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("KBO::State::innerResult");

  ASS_NEQ(tl1, tl2);
  ASS(!TermList::sameTopFunctor(tl1,tl2));

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(tl1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(tl2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else {
      res=_kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    } else if(*pnum==1) {
      _posNum++;
    }
  } else {
    if(*pnum==0) {
      _posNum--;
    } else if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::State::traverse(TermList tl,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    _weightDiff+=_kbo._variableWeight*coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.functionSymbolWeight(t->functor())*coef;

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      _weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::State::traverse(Term* t1, Term* t2)
{
  CALL("KBO::State::traverse");
  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<TermList*> stack(32);
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!stack.isEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
	lexValidDepth=depth;
	if(_weightDiff!=0) {
	  _lexResult=_weightDiff>0 ? GREATER : LESS;
	}
	_lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      ASS(ss->term()->arity());
      stack.push(ss->term()->args());
      stack.push(tt->term()->args());
      depth++;
    } else {
      traverse(*ss,1);
      traverse(*tt,-1);
      if(_lexResult==EQUAL) {
	_lexResult=innerResult(*ss, *tt);
	lexValidDepth=depth;
	ASS(_lexResult!=EQUAL);
	ASS(_lexResult!=GREATER_EQ);
	ASS(_lexResult!=LESS_EQ);
      }
    }
  }
  ASS_EQ(depth,0);
}


/**
 * Create a KBO object.
 */
KBO::KBO(Problem& prb, const Options& opt)
 : KBOBase(prb, opt)
{
  CALL("KBO::KBO");

  _variableWeight = 1;
  _defaultSymbolWeight = 1;

  _state=new State(this);
}

KBO::~KBO()
{
  CALL("KBO::~KBO");

  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::compare(Literal* l1, Literal* l2) const
{
  CALL("KBO::compare(Literal*...)");
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
    int lev1 = predicateLevel(p1);
    int lev2 = predicateLevel(p2);
    if (lev1 > lev2) {
      res=GREATER;
      goto fin;
    }
    if (lev2 > lev1) {
      res=LESS;
      goto fin;
    }
  }

  if(l1->isEquality()) {
    ASS(l2->isEquality());
    return compareEqualities(l1, l2);
  }
  ASS(!l1->isEquality());

  {
    ASS(_state);
    State* state=_state;
#if VDEBUG
    //this is to make sure _state isn't used while we're using it
    _state=0;
#endif
    state->init();
    if(p1!=p2) {
      TermList* ts;
      ts=l1->args();
      while(!ts->isEmpty()) {
	state->traverse(*ts,1);
	ts=ts->next();
      }
      ts=l2->args();
      while(!ts->isEmpty()) {
	state->traverse(*ts,-1);
	ts=ts->next();
      }
    } else {
      state->traverse(l1,l2);
    }

    res=state->result(l1,l2);
#if VDEBUG
    _state=state;
#endif
  }

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
} // KBO::compare()

Ordering::Result KBO::compare(TermList tl1, TermList tl2) const
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
    }
  }
  if(tl2.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
    }
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(t1->functor()==t2->functor()) {
    state->traverse(t1,t2);
  } else {
    state->traverse(tl1,1);
    state->traverse(tl2,-1);
  }
  Result res=state->result(t1,t2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

int KBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;

  if(env.signature->functionColored(fun)) {
    weight *= COLORED_WEIGHT_BOOST;
  }

  return weight;
}

//////////////////////////////////////////////////
// KBOBase class
//////////////////////////////////////////////////

/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality). If a predicate is colored, its level is multiplied by
 * the COLORED_LEVEL_BOOST value.
 * @since 11/05/2008 Manchester
 */
int KBOBase::predicateLevel (unsigned pred) const
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
} // KBO::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 * @since 11/05/2008 Manchester
 */
int KBOBase::predicatePrecedence (unsigned pred) const
{
  int res=pred >= _predicates ? (int)pred : _predicatePrecedences[pred];
  if(NONINTERPRETED_PRECEDENCE_BOOST) {
    ASS_EQ(NONINTERPRETED_PRECEDENCE_BOOST & 1, 0); // an even number

    bool intp = env.signature->getPredicate(pred)->interpreted();
    res *= 2;
    return intp ? res+1 : res+NONINTERPRETED_PRECEDENCE_BOOST;
  }
  return res;
} // KBO::predicatePrecedences

Comparison KBOBase::compareFunctors(unsigned fun1, unsigned fun2) const
{
  CALL("KBOBase::compareFunctors");

  if(fun1==fun2) {
    return Lib::EQUAL;
  }
  switch(compareFunctionPrecedences(fun1, fun2)) {
  case GREATER: return Lib::GREATER;
  case LESS: return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Compare precedences of two function symbols
 */
Ordering::Result KBOBase::compareFunctionPrecedences(unsigned fun1, unsigned fun2) const
{
  CALL("KBOBase::compareFunctionPrecedences");
  ASS_NEQ(fun1, fun2);

  // $$false is the smallest
  if (env.signature->isFoolConstantSymbol(false,fun1)) {
    return LESS;
  }
  if (env.signature->isFoolConstantSymbol(false,fun2)) {
    return GREATER;
  }

  // $$true is the second smallest
  if (env.signature->isFoolConstantSymbol(true,fun1)) {
    return LESS;
  }

  if (env.signature->isFoolConstantSymbol(true,fun2)) {
    return GREATER;
  }

  Signature::Symbol* s1=env.signature->getFunction(fun1);
  Signature::Symbol* s2=env.signature->getFunction(fun2);
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

  if (!s1->numericConstant() || !s2->numericConstant()) {
    return fromComparison(Int::compare(fun1, fun2));
  }

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
    ASS_REP(s2->rationalConstant() || s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->integerConstant()) {
    ASS_REP(s1->rationalConstant() || s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else if(s1->rationalConstant()) {
    ASS_REP(s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->rationalConstant()) {
    ASS_REP(s1->realConstant(), s1->name());
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
 * Create a KBOBase object.
 */
KBOBase::KBOBase(Problem& prb, const Options& opt)
  : _predicates(env.signature->predicates()),
    _functions(env.signature->functions()),
    _predicateLevels(_predicates),
    _predicatePrecedences(_predicates),
    _functionPrecedences(_functions)
{
  CALL("KBOBase::KBOBase");
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
