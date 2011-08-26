/**
 * @file EqualityProxy.cpp
 * Implements class EqualityProxy.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "EqualityProxy.hpp"

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;

ZIArray<unsigned> EqualityProxy::s_proxyPredicates = 0;

EqualityProxy::EqualityProxy(Options::EqualityProxy opt)
: _opt(opt)
{
  CALL("EqualityProxy::EqualityProxy/1");

  init();
}

void EqualityProxy::init()
{
  CALL("EqualityProxy::init");

  switch (_opt) {
  case Options::EP_R:
  case Options::EP_RS:
  case Options::EP_RST:
  case Options::EP_RSTC:
    _rst = true;
    break;
  case Options::EP_ON:
    _rst = false;
    break;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Apply the equality proxy transformation to a problem.
 */
void EqualityProxy::apply(Problem& prb)
{
  CALL("EqualityProxy::apply(Problem&)");

  bool hadEquality = prb.hasEquality();

  apply(prb.units());
  prb.invalidateByRemoval();
  if(_rst) {
    prb.reportEqualityEliminated();
  }

  if(hadEquality) {
    switch(_opt) {
      case Options::EP_R:
      case Options::EP_RS:
      case Options::EP_RST:
	prb.reportIncompleteTransformation();
	break;
      default:
	break;
    }
  }

}

/**
 * Apply the equality proxy transformation to a list of clauses.
 */
void EqualityProxy::apply(UnitList*& units)
{
  CALL("EqualityProxy::apply(UnitList*&)");

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    Clause* cl2=apply(cl);
    if(cl!=cl2) {
      uit.replace(cl2);
    }
  }

  addAxioms(units);
} // apply

void EqualityProxy::addLocalAxioms(UnitList*& units, unsigned sort)
{
  CALL("EqualityProxy::addLocalAxioms");

  {
    Clause* axR = new(1) Clause(1, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM1));
    (*axR)[0]=makeProxyLiteral(true,TermList(0,false),TermList(0,false), sort);
    UnitList::push(axR,units);
  }

  if(_opt==Options::EP_RS || _opt==Options::EP_RST || _opt==Options::EP_RSTC) {
    Clause* axS = new(2) Clause(2, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axS)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false), sort);
    (*axS)[1]=makeProxyLiteral(true,TermList(1,false),TermList(0,false), sort);
    UnitList::push(axS,units);
  }
  if(_opt==Options::EP_RST || _opt==Options::EP_RSTC) {
    Clause* axT = new(3) Clause(3, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axT)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false), sort);
    (*axT)[1]=makeProxyLiteral(false,TermList(1,false),TermList(2,false), sort);
    (*axT)[2]=makeProxyLiteral(true,TermList(0,false),TermList(2,false), sort);
    UnitList::push(axT,units);
  }

  if(!_rst) {
    Clause* axE = new(2) Clause(2, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axE)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false), sort);
    (*axE)[1]=Literal::createVariableEquality(true,TermList(0,false),TermList(1,false), sort);
    UnitList::push(axE,units);
  }
}

/**
 * Add axioms for the equality proxy predicates
 *
 * We add axioms only for the sorts for which the equality proxy predicates were created.
 * Therefore this function should be called only after the equality proxy replacement
 * is performed on the whole problem, so that the needed equality proxy predicates are
 * created at this time.
 */
void EqualityProxy::addAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addAxioms");

  //if we're adding congruence axioms, we need to add them before adding the local axioms.
  //Local axioms are added only for sorts on which euality is used, and the congruence axioms
  //may spread the equality use into new sorts
  if(_opt==Options::EP_RSTC) {
    addCongruenceAxioms(units);
  }

  unsigned proxyPredArrSz = s_proxyPredicates.size();
  for(unsigned sort=0; sort<proxyPredArrSz; sort++) {
    if(haveProxyPredicate(sort)) {
      addLocalAxioms(units, sort);
    }
  }
} // addAxioms

/**
 *
 *
 * symbolType is the type of symbol for whose arguments we're generating the
 * equalities.
 */
bool EqualityProxy::getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2, BaseType* symbolType, bool skipSortsWithoutEquality)
{
  CALL("EqualityProxy::getArgumentEqualityLiterals");
  ASS_EQ(cnt, symbolType->arity());

  lits.reset();
  vars1.reset();
  vars2.reset();

  for(unsigned i=0; i<cnt; i++) {
    TermList v1(2*i, false);
    TermList v2(2*i+1, false);
    unsigned sort = symbolType->arg(i);
    if(!skipSortsWithoutEquality || haveProxyPredicate(sort)) {
      lits.push(makeProxyLiteral(false, v1, v2, sort));
      vars1.push(v1);
      vars2.push(v2);
    }
    else {
      vars1.push(v1);
      vars2.push(v1);
    }
  }
  return lits.isNonEmpty();
}

void EqualityProxy::addCongruenceAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addCongruenceAxioms");
  //TODO: skip UPDR predicates!!!
  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;

  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    Signature::Symbol* fnSym = env.signature->getFunction(i);
    unsigned arity = fnSym->arity();
    if(arity==0) {
      continue;
    }
    FunctionType* fnType = fnSym->fnType();
    getArgumentEqualityLiterals(arity, lits, vars1, vars2, fnType, false);
    Term* t1 = Term::create(i, arity, vars1.begin());
    Term* t2 = Term::create(i, arity, vars2.begin());
    lits.push(makeProxyLiteral(true, TermList(t1), TermList(t2), fnType->result()));

    Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    UnitList::push(cl,units);
  }

  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    unsigned arity = predSym->arity();
    if(predSym->equalityProxy() || predSym->arity()==0) {
      continue;
    }
    if(!getArgumentEqualityLiterals(arity, lits, vars1, vars2, predSym->predType(), true)) {
      continue;
    }
    lits.push(Literal::create(i, arity, false, false, vars1.begin()));
    lits.push(Literal::create(i, arity, true, false, vars2.begin()));

    Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    UnitList::push(cl,units);
  }
}


Clause* EqualityProxy::apply(Clause* cl)
{
  CALL("EqualityProxy::apply(Clause*)");

  unsigned clen=cl->length();

  static Stack<Literal*> resLits(8);
  resLits.reset();

  bool modified=false;
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    Literal* rlit=apply(lit);
    resLits.push(rlit);
    modified|= rlit!=lit;
  }
  if(!modified) {
    return cl;
  }

  Inference* inf = new Inference1(Inference::EQUALITY_PROXY_REPLACEMENT, cl);

  Clause* res = new(clen) Clause(clen, cl->inputType(), inf);
  res->setAge(cl->age());

  for(unsigned i=0;i<clen;i++) {
    (*res)[i] = resLits[i];
  }

  return res;
}

Literal* EqualityProxy::apply(Literal* lit)
{
  CALL("EqualityProxy::apply(Literal*)");

  if(!lit->isEquality()) {
    return lit;
  }
  if(lit->isPositive() && !_rst &&
	  (!lit->nthArgument(0)->isVar() || !lit->nthArgument(1)->isVar())) {
    return lit;
  }

  unsigned sort = SortHelper::getEqualityArgumentSort(lit);
  return makeProxyLiteral(lit->polarity(), *lit->nthArgument(0), *lit->nthArgument(1), sort);
}

bool EqualityProxy::haveProxyPredicate(unsigned sort) const
{
  CALL("EqualityProxy::haveProxyPredicate");

  return s_proxyPredicates[sort]!=0;
}

unsigned EqualityProxy::getProxyPredicate(unsigned sort)
{
  CALL("EqualityProxy::getProxyPredicate");
  ASS_L(sort, env.sorts->sorts());

  if(s_proxyPredicates[sort]!=0) {
    return s_proxyPredicates[sort];
  }
  unsigned newPred = env.signature->addFreshPredicate(2,"sQ","eqProxy");
  Signature::Symbol* predSym = env.signature->getPredicate(newPred);
  unsigned predDomain[] = { sort, sort };
  BaseType* predType = PredicateType::makeType(2, predDomain, Sorts::SRT_BOOL);
  predSym->setType(predType);
  predSym->markEqualityProxy();

  s_proxyPredicates[sort] = newPred;
  return newPred;
}

Literal* EqualityProxy::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1)
{
  CALL("EqualityProxy::createProxyLiteral/3");

  unsigned sort;
  if(arg0.isTerm()) {
    sort = SortHelper::getResultSort(arg0.term());
  }
  else {
    ASS(arg1.isTerm()); //if we have two variables, we need to use the other makeProxyLiteral and specify the sort
    sort = SortHelper::getResultSort(arg1.term());
  }
  return makeProxyLiteral(polarity, arg0, arg1, sort);
}

Literal* EqualityProxy::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, unsigned sort)
{
  CALL("EqualityProxy::createProxyLiteral/4");

  unsigned pred = getProxyPredicate(sort);

  TermList args[] = {arg0, arg1};
  return Literal::create(pred, 2, polarity, false, args);
}

