/**
 * @file EqualityProxy.cpp
 * Implements class EqualityProxy.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "EqualityProxy.hpp"

namespace Shell
{
using namespace std;
using namespace Lib;
using namespace Kernel;

unsigned EqualityProxy::s_proxyPredicate = 0;

EqualityProxy::EqualityProxy()
: _opt(env.options->equalityProxy())
{
  CALL("EqualityProxy::EqualityProxy/0");

  init();
}

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
  if(!s_proxyPredicate) {
    string proxy("sQ1_eqProxy");
    bool added;
    unsigned predNum;
    for(;;) {
      predNum=env.signature->addPredicate(proxy,2,added);
      if(added) {
	break;
      }
      proxy += "_";
    };
    s_proxyPredicate=predNum;
  }
}


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
}


void EqualityProxy::addAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addAxioms");

  {
    Clause* axR = new(1) Clause(1, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM1));
    (*axR)[0]=makeProxyLiteral(true,TermList(0,false),TermList(0,false));
    UnitList::push(axR,units);
  }

  if(_opt==Options::EP_RS || _opt==Options::EP_RST || _opt==Options::EP_RSTC) {
    Clause* axS = new(2) Clause(2, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axS)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false));
    (*axS)[1]=makeProxyLiteral(true,TermList(1,false),TermList(0,false));
    UnitList::push(axS,units);
  }
  if(_opt==Options::EP_RST || _opt==Options::EP_RSTC) {
    Clause* axT = new(3) Clause(3, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axT)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false));
    (*axT)[1]=makeProxyLiteral(false,TermList(1,false),TermList(2,false));
    (*axT)[2]=makeProxyLiteral(true,TermList(0,false),TermList(2,false));
    UnitList::push(axT,units);
  }
  if(_opt==Options::EP_RSTC) {
    addCongruenceAxioms(units);
  }

  if(!_rst) {
    Clause* axE = new(2) Clause(2, Clause::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    (*axE)[0]=makeProxyLiteral(false,TermList(0,false),TermList(1,false));
    (*axE)[1]=Literal::createEquality(true,TermList(0,false),TermList(1,false));
    UnitList::push(axE,units);
  }
}

void EqualityProxy::getVariableEqualityLiterals(unsigned cnt, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2)
{
  CALL("EqualityProxy::getVariableEqualityLiterals");

  lits.reset();
  vars1.reset();
  vars2.reset();

  for(unsigned i=0; i<cnt; i++) {
    TermList v1(2*i, false);
    TermList v2(2*i+1, false);
    lits.push(makeProxyLiteral(false, v1, v2));
    vars1.push(v1);
    vars2.push(v2);
  }
}

void EqualityProxy::addCongruenceAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addCongruenceAxioms");

  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;

  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    unsigned arity = env.signature->predicateArity(i);
    if(i==s_proxyPredicate || !arity) {
      continue;
    }
    getVariableEqualityLiterals(arity, lits, vars1, vars2);
    lits.push(Literal::create(i, arity, false, false, vars1.begin()));
    lits.push(Literal::create(i, arity, true, false, vars2.begin()));

    Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::EQUALITY_PROXY_AXIOM2));
    UnitList::push(cl,units);
  }

  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    unsigned arity = env.signature->functionArity(i);
    if(!arity) {
      continue;
    }
    getVariableEqualityLiterals(arity, lits, vars1, vars2);
    Term* t1 = Term::create(i, arity, vars1.begin());
    Term* t2 = Term::create(i, arity, vars2.begin());
    lits.push(makeProxyLiteral(true, TermList(t1), TermList(t2)));

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

  return makeProxyLiteral(lit->polarity(),*lit->nthArgument(0),*lit->nthArgument(1));
}

Literal* EqualityProxy::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1)
{
  CALL("EqualityProxy::createProxyLiteral");

  Literal* res = new(2) Literal(s_proxyPredicate,2,polarity,false);
  *res->nthArgument(0)=arg0;
  *res->nthArgument(1)=arg1;
  res = env.sharing->insert(res);
  return res;
}

}
