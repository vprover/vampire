
/*
 * File EqualityAxiomatizer.cpp.
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
 * @file EqualityAxiomatizer.cpp
 * Implements class EqualityAxiomatizer.
 */

#include "Lib/Environment.hpp"
#include "Lib/ImplicationSetClosure.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "EqualityAxiomatizer.hpp"

namespace Shell
{

/**
 * Apply the equality proxy transformation to a problem.
 */
void EqualityAxiomatizer::apply(Problem& prb)
{
  CALL("EqualityAxiomatizer::apply(Problem&)");

  if(!prb.hasEquality()) {
    return;
  }

  scan(prb.units());

  UnitList* axioms = getAxioms();
  prb.addUnits(axioms);
}

/**
 * Apply the equality proxy transformation to a list of clauses.
 */
void EqualityAxiomatizer::apply(UnitList*& units)
{
  CALL("EqualityAxiomatizer::apply(UnitList*&)");

  scan(units);

  UnitList* axioms = getAxioms();
  units = UnitList::concat(axioms, units);
}

void EqualityAxiomatizer::scan(Literal* lit)
{
  CALL("EqualityAxiomatizer::scan(Literal*)");

  if(lit->arity()==0) {
    return;
  }
  if(lit->isEquality()) {
    unsigned eqSort = SortHelper::getEqualityArgumentSort(lit);
    _eqSorts.insert(eqSort);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "eq sort "<<env.sorts->sortName(eqSort)<<" added because of "<<(*lit) << std::endl;
      env.endOutput();
    }    
  }
  else {
    _preds.insert(lit->functor());
  }
  NonVariableIterator nvit(lit);
  while(nvit.hasNext()) {
    TermList t = nvit.next();
    ASS(t.isTerm());
    Term* trm = t.term();
    if(trm->arity()==0) {
      continue;
    }
    _fns.insert(trm->functor());
  }
}

/**
 * Determine for which sorts equality is relevant
 *
 * Equality is relevant for sorts that have equality literals (these were
 * found by the scan() functions), and for sorts that are range of a function
 * with equality-relevant sort in their domain.
 */
void EqualityAxiomatizer::saturateEqSorts()
{
  CALL("EqualityAxiomatizer::saturateEqSorts");

  if(_eqSorts.isEmpty()) { return; }

  ImplicationSetClosure<unsigned> isc;

  isc.addFromIterator(SortSet::Iterator(_eqSorts));

  SymbolSet::Iterator fit(_fns);
  while(fit.hasNext()) {
    unsigned fn = fit.next();
    FunctionType* ft = env.signature->getFunction(fn)->fnType();
    unsigned rngSort = ft->result();
    unsigned arity = ft->arity();
    for(unsigned ai = 0; ai<arity; ++ai) {
      unsigned argSort = ft->arg(ai);
      if(argSort==rngSort) {
	continue;
      }
      isc.addImplication(argSort, rngSort);
    }
  }

  ImplicationSetClosure<unsigned>::Iterator implIt(isc);
  while(implIt.hasNext()) {
    unsigned eqSort = implIt.next();
    if(_eqSorts.insert(eqSort)) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "eq sort "<<env.sorts->sortName(eqSort)<<" added by implications" << std::endl;
        env.endOutput();
      }
    }
  }

}

void EqualityAxiomatizer::scan(UnitList* units)
{
  CALL("EqualityAxiomatizer::scan(UnitList*)");

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS_REP(u->isClause(),*u);
    Clause::Iterator cit(*static_cast<Clause*>(u));
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      scan(lit);
    }
  }
  saturateEqSorts();
}

void EqualityAxiomatizer::addLocalAxioms(UnitList*& units, unsigned sort)
{
  CALL("EqualityAxiomatizer::addLocalAxioms");

  {
    Clause* axR = new(1) Clause(1, Clause::AXIOM, new Inference0(Inference::EQUALITY_PROXY_AXIOM2));
    (*axR)[0]=Literal::createEquality(true,TermList(0,false),TermList(0,false), sort);
    UnitList::push(axR,units);
  }

  if(_opt==Options::EqualityProxy::RST || _opt==Options::EqualityProxy::RSTC) {
    Clause* axT = new(3) Clause(3, Clause::AXIOM, new Inference0(Inference::EQUALITY_PROXY_AXIOM2));
    (*axT)[0]=Literal::createEquality(false,TermList(0,false),TermList(1,false), sort);
    (*axT)[1]=Literal::createEquality(false,TermList(1,false),TermList(2,false), sort);
    (*axT)[2]=Literal::createEquality(true,TermList(0,false),TermList(2,false), sort);
    UnitList::push(axT,units);
  }
}

UnitList* EqualityAxiomatizer::getAxioms()
{
  CALL("EqualityAxiomatizer::getAxioms");

  UnitList* res = 0;


  SortSet::Iterator sit(_eqSorts);
  while(sit.hasNext()) {
    unsigned srt = sit.next();
    addLocalAxioms(res, srt);
  }

  if(_opt==Options::EqualityProxy::RSTC) {
    addCongruenceAxioms(res);
  }

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    ostream& out = env.out();
    out << "Sorts using equality:" << endl;
    
    SortSet::Iterator sit2(_eqSorts);
    while(sit2.hasNext()) {
      unsigned srt = sit2.next();
      out << env.sorts->sortName(srt);
      if(sit2.hasNext()) {
        out << ", ";
      }
    }
    out << endl;

    out << "Added axioms:" << endl;
    UnitList::Iterator uit(res);
    while(uit.hasNext()) {
      out << (*uit.next()) << endl;
    }
        
    env.endOutput();
  }
                 
  return res;
}

/**
 *
 *
 * symbolType is the type of symbol for whose arguments we're generating the
 * equalities.
 */
bool EqualityAxiomatizer::getArgumentEqualityLiterals(BaseType* symbolType, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2)
{
  CALL("EqualityAxiomatizer::getArgumentEqualityLiterals");

  unsigned cnt = symbolType->arity();
  lits.reset();
  vars1.reset();
  vars2.reset();

  for(unsigned i=0; i<cnt; i++) {
    TermList v1(2*i, false);
    TermList v2(2*i+1, false);
    unsigned sort = symbolType->arg(i);
    if(_eqSorts.contains(sort)) {
      lits.push(Literal::createEquality(false, v1, v2, sort));
      vars1.push(v1);
      vars2.push(v2);
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "sort "<<env.sorts->sortName(sort)<<" lead to equality "<<(*lits.top()) << std::endl;
        env.endOutput();
      }            
    }
    else {
      vars1.push(v1);
      vars2.push(v1);
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "sort "<<env.sorts->sortName(sort)<<" did not use equality" << std::endl;
        env.endOutput();
      }
    }
  }
  return lits.isNonEmpty();
}


Clause* EqualityAxiomatizer::getFnCongruenceAxiom(unsigned fn)
{
  CALL("EqualityAxiomatizer::getFnCongruenceAxiom");

  static Stack<TermList> vars1;
  static Stack<TermList> vars2;
  static LiteralStack lits;

  vars1.reset();
  vars2.reset();
  lits.reset();

  Signature::Symbol* fnSym = env.signature->getFunction(fn);
  FunctionType* fnType = fnSym->fnType();

  if(!_eqSorts.contains(fnType->result())) {
    return 0;
  }

  unsigned arity = fnSym->arity();
  ASS_G(fnSym->arity(),0); //we've checked for this during collection of function symbols

  if(!getArgumentEqualityLiterals(fnType, lits, vars1, vars2)) {
    return 0;
  }
  Term* t1 = Term::create(fn, arity, vars1.begin());
  Term* t2 = Term::create(fn, arity, vars2.begin());
  lits.push(Literal::createEquality(true, TermList(t1), TermList(t2), fnType->result()));

  return Clause::fromStack(lits, Unit::AXIOM, new Inference0(Inference::EQUALITY_PROXY_AXIOM2));
}

Clause* EqualityAxiomatizer::getPredCongruenceAxiom(unsigned pred)
{
  CALL("EqualityAxiomatizer::getPredCongruenceAxiom");
  ASS_NEQ(pred,0);

  static Stack<TermList> vars1;
  static Stack<TermList> vars2;
  static LiteralStack lits;

  vars1.reset();
  vars2.reset();
  lits.reset();

  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  unsigned arity = predSym->arity();
  ASS_G(arity,0);
  if(!getArgumentEqualityLiterals(predSym->predType(), lits, vars1, vars2)) {
    return 0;
  }
  lits.push(Literal::create(pred, arity, false, false, vars1.begin()));
  lits.push(Literal::create(pred, arity, true, false, vars2.begin()));

  return Clause::fromStack(lits, Unit::AXIOM, new Inference0(Inference::EQUALITY_PROXY_AXIOM2));
}

void EqualityAxiomatizer::addCongruenceAxioms(UnitList*& units)
{
  CALL("EqualityAxiomatizer::addCongruenceAxioms");
  ASS(_opt==Options::EqualityProxy::RSTC);

  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;

  SymbolSet::Iterator fit(_fns);
  while(fit.hasNext()) {
    unsigned fn = fit.next();
    Clause* cl = getFnCongruenceAxiom(fn);
    if(!cl) { continue; }
    UnitList::push(cl,units);
  }

  SymbolSet::Iterator pit(_preds);
  while(pit.hasNext()) {
    unsigned pred = pit.next();
    Clause* cl = getPredCongruenceAxiom(pred);
    if(!cl) { continue; }
    UnitList::push(cl,units);
  }
}


}
