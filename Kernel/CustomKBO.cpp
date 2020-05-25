/*
 * File CustomKBO.cpp.
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

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "CustomKBO.hpp"
#include "Signature.hpp"

#include <cstdlib>

#define COLORED_WEIGHT_BOOST 0x10000

namespace Kernel {

using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class CustomKBO::State
{
public:
  /** Initialise the state */
  State(CustomKBO const& kbo)
    : _kbo(kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  CLASS_NAME(CustomKBO::State);
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
  CustomKBO const& _kbo;
  /** The variable counters */
}; // class CustomKBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result CustomKBO::State::result(Term* t1, Term* t2)
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
  //CustomKBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result CustomKBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("CustomKBO::State::innerResult");

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

void CustomKBO::State::recordVariable(unsigned var, int coef)
{
  CALL("CustomKBO::State::recordVariable");
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

void CustomKBO::State::traverse(TermList tl,int coef)
{
  CALL("CustomKBO::State::traverse(TermList...)");

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

void CustomKBO::State::traverse(Term* t1, Term* t2)
{
  CALL("CustomKBO::State::traverse");
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
 * Create a CustomKBO object.
 */
CustomKBO::CustomKBO(Problem& prb, const Options& opt)
 : PrecedenceOrdering(prb, opt)
 , _symbolWeights()
{
  CALL("CustomKBO::CustomKBO");

  _variableWeight = 1;
  _defaultSymbolWeight = 1;

  _state=new State(*this);

  // TODO: extract into separate function that takes a string argument.
  // Parse weights from option string, example: f=5,g/2=27
  vmap<unsigned, int> weights;
  vstring const& weights_str = opt.customKBOWeights();
  const char* s = weights_str.data();
  const char* s_end = s + weights_str.length();
  while (s < s_end) {
    // Read name
    const char* s2 = s;
    while (s2 < s_end && *s2 != '=') {
      s2 += 1;
    }
    if (s2 == s_end) {
      USER_ERROR("error parsing symbol weights: expected '='");
    }
    vstring name(s, s2 - s);
    s = s2 + 1;
    std::cerr << "name = " << name << std::endl;

    // TODO: parse arity

    // Read weight
    char *w_end;
    int weight = std::strtol(s, &w_end, 10);
    if (errno != 0) {
      int e = errno;
      errno = 0;
      vstring msg = vstring("error parsing symbol weights: unable to parse weight at \"") + s + "\" (" + std::strerror(e) + ")";
      USER_ERROR(msg);
    }
    s = w_end;

    std::cerr << "weight = " << weight << std::endl;

    // delimiter after weight
    if (s < s_end && *s != ',') {
      USER_ERROR("error parsing symbol weights: expected ','");
    }
    s += 1;

    // Find function number
    // Note that Signature only stores (function, arity) pairs,
    // so we do this the hacky way by iterating over all registered functions.
    bool found = false;
    for (unsigned fn = 0; fn < env.signature->functions(); ++fn) {
      if (env.signature->functionName(fn) == name) {
        if (found) {
          vstringstream msg;
          msg << "error parsing symbol weights: name \"" << name
            << "\" is ambigous, please specify arity as well "
            << "(example: " << name << "/2=" << weight << ")";
          USER_ERROR(msg.str());
        }
        found = true;
        const auto res = weights.insert({fn, weight});
        bool inserted = res.second;
        if (!inserted) {
          USER_ERROR("error parsing symbol weights: weight for symbol \"" + name + "\" has been specified twice");
        }
      }
    }
    if (!found) {
      USER_ERROR("error parsing symbol weights: function symbol \"" + name + "\" is not present in the signature");
    }
  }

  if (!weights.empty()) {
    unsigned max_fn = weights.rbegin()->first;
    _symbolWeights.resize(max_fn + 1, _defaultSymbolWeight);
    for (auto p : weights) {
      _symbolWeights[p.first] = p.second;
    }
  }

  std::cerr << "symbolWeights = [ ";
  for (auto it = _symbolWeights.cbegin(); it != _symbolWeights.cend(); ++it) {
    std::cerr << *it << " ";
  }
  std::cerr << "]" << std::endl;
}

CustomKBO::~CustomKBO()
{
  CALL("CustomKBO::~CustomKBO");

  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result CustomKBO::comparePredicates(Literal* l1, Literal* l2) const
{
  CALL("CustomKBO::comparePredicates");
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  Result res;
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
  return res;
} // CustomKBO::comparePredicates()

Ordering::Result CustomKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("CustomKBO::compare(TermList)");

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

int CustomKBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;
  if (fun < _symbolWeights.size()) {
    weight = _symbolWeights[fun];
  }

  if(env.signature->functionColored(fun)) {
    weight *= COLORED_WEIGHT_BOOST;
  }

  return weight;
}


}
