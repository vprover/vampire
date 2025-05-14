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
 * @file EqualityProxy.cpp
 * Implements class EqualityProxy.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "EqualityProxyMono.hpp"

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;

DHMap<TermList, unsigned> EqualityProxyMono::s_proxyPredicates;
DHMap<unsigned, TermList> EqualityProxyMono::s_proxyPredicateSorts;
DHMap<TermList, Unit*> EqualityProxyMono::s_proxyPremises;

/**
 * Constructor, simply memorizes the value of the equality proxy option.
 */
EqualityProxyMono::EqualityProxyMono(Options::EqualityProxy opt)
: _opt(opt)
{
  ASS(opt != Options::EqualityProxy::OFF);
} // EqualityProxy::EqualityProxy

/**
 * Apply the equality proxy transformation to a problem. The problem must only contain
 * clauses, no formulas.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxyMono::apply(Problem& prb)
{
  bool hadEquality = prb.hasEquality();

  apply(prb.units());
  prb.invalidateByRemoval();
  prb.reportEqualityEliminated();

  if (hadEquality) {
    switch(_opt) {
      case Options::EqualityProxy::R:
      case Options::EqualityProxy::RS:
      case Options::EqualityProxy::RST:
	prb.reportIncompleteTransformation();
	break;
      default:
	break;
    }
  }
} // EqualityProxy::apply

/**
 * Apply the equality proxy transformation to a list of clauses.
 * This function first iterates through clauses and replaces them with clauses where
 * equality is replaced by the proxy and then adds an axiomatisation of the proxy
 * predicate.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxyMono::apply(UnitList*& units)
{
  UnitList::DelIterator uit(units);
  while (uit.hasNext()) {
    Unit* unit = uit.next();
    ASS (unit->isClause());
    Clause* cl = static_cast<Clause*>(unit);
    Clause* cl2 = apply(cl);
    if (cl != cl2) {
      uit.replace(cl2);
    }
  }

  addAxioms(units);
} // apply

/**
 * Add reflexivity, symmetry and transitivity axioms depending on the value of the 
 * equality proxy option.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxyMono::addLocalAxioms(UnitList*& units, TermList sort)
{
  // reflexivity
  Stack<Literal*> lits;
  lits.push(makeProxyLiteral(true,TermList(0,false),TermList(0,false), sort));
  UnitList::push(createEqProxyAxiom(lits),units);

  // symmetry
  if (_opt == Options::EqualityProxy::RS || _opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(0,false),TermList(1,false), sort));
    lits.push(makeProxyLiteral(true,TermList(1,false),TermList(0,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
  // transitivity
  if (_opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(0,false),TermList(1,false), sort));
    lits.push(makeProxyLiteral(false,TermList(1,false),TermList(2,false), sort));
    lits.push(makeProxyLiteral(true,TermList(0,false),TermList(2,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
} // EqualityProxy::addLocalAxioms

/**
 * Add axioms for the equality proxy predicates
 *
 * We add axioms only for the sorts for which the equality proxy predicates were created.
 * Therefore this function should be called only after the equality proxy replacement
 * is performed on the whole problem, so that the needed equality proxy predicates are
 * created at this time.
 */
void EqualityProxyMono::addAxioms(UnitList*& units)
{
  // if we're adding congruence axioms, we need to add them before adding the local axioms.
  // Local axioms are added only for sorts on which equality is used, and the congruence axioms
  // may spread the equality use into new sorts
  if (_opt == Options::EqualityProxy::RSTC) {
    addCongruenceAxioms(units);
  }

  DHMap<TermList, unsigned>::Iterator it(s_proxyPredicates);
  while(it.hasNext()) {
    addLocalAxioms(units, it.nextKey());
  }
} // addAxioms

/**
 *
 *
 * symbolType is the type of symbol for whose arguments we're generating the
 * equalities.
 */
bool EqualityProxyMono::getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2, OperatorType* symbolType, bool skipSortsWithoutEquality)
{
  ASS_EQ(cnt, symbolType->arity());

  lits.reset();
  vars1.reset();
  vars2.reset();

  for (unsigned i=0; i<cnt; i++) {
    TermList v1(2*i, false);
    TermList v2(2*i+1, false);
    TermList sort = symbolType->arg(i);
    if (!skipSortsWithoutEquality || haveProxyPredicate(sort)) {
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

/**
 * For every symbol occurring in env.signature, add to the units equality congruence axioms
 * for this symbol.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxyMono::addCongruenceAxioms(UnitList*& units)
{
  // This is Krystof Hoder's comment:
  // TODO: skip UPDR predicates!!!
  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;

  unsigned funs = env.signature->functions();
  for (unsigned i=0; i<funs; i++) {
    Signature::Symbol* fnSym = env.signature->getFunction(i);
    // can axiomatise equality _before_ preprocessing, so skip (some) introduced symbols
    if(!fnSym->usageCnt() || fnSym->skipCongruence())
      continue;
    unsigned arity = fnSym->arity();
    if (arity == 0) {
      continue;
    }
    OperatorType* fnType = fnSym->fnType();
    getArgumentEqualityLiterals(arity, lits, vars1, vars2, fnType, false);
    Term* t1 = Term::create(i, arity, vars1.begin());
    Term* t2 = Term::create(i, arity, vars2.begin());
    lits.push(makeProxyLiteral(true, TermList(t1), TermList(t2), fnType->result()));

    Clause* cl = createEqProxyAxiom(lits);
    UnitList::push(cl,units);
  }

  unsigned preds = env.signature->predicates();
  for (unsigned i = 1; i < preds; i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    // can axiomatise equality _before_ preprocessing, so skip (some) introduced symbols
    if(!predSym->usageCnt() || predSym->skipCongruence())
      continue;
    unsigned arity = predSym->arity();
    if (arity == 0) {
      continue;
    }
    if (!getArgumentEqualityLiterals(arity, lits, vars1, vars2, predSym->predType(), true)) {
      continue;
    }
    lits.push(Literal::create(i, arity, false, vars1.begin()));
    lits.push(Literal::create(i, arity, true, vars2.begin()));

    Clause* cl = createEqProxyAxiom(lits);
    UnitList::push(cl,units);
  }
}

/**
 * Replace in the clause all occurrences of equalities by the equality proxy predicate.
 * If the clause did not change, return the clause, otherwise the modified clause.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
Clause* EqualityProxyMono::apply(Clause* cl)
{
  UnitStack proxyPremises;
  RStack<Literal*> resLits;

  bool modified = false;
  for (Literal* lit : cl->iterLits()) {
    Literal* rlit=apply(lit);
    resLits->push(rlit);
    if (rlit != lit) {
      ASS(lit->isEquality());
      modified = true;
      TermList srt = s_proxyPredicateSorts.get(rlit->functor());
      Unit* prem = s_proxyPremises.get(srt);
      proxyPremises.push(prem);
    }
  }
  if (!modified) {
    return cl;
  }

  Clause* res;
  ASS(proxyPremises.isNonEmpty());
  if (proxyPremises.size() == 1) {
    res = Clause::fromStack(*resLits,
        NonspecificInference2(InferenceRule::EQUALITY_PROXY_REPLACEMENT, cl, proxyPremises.top()));
  }
  else {
    UnitList* prems = 0;
    UnitList::pushFromIterator(UnitStack::ConstIterator(proxyPremises),prems);
    UnitList::push(cl,prems);

    res = Clause::fromStack(*resLits,
        NonspecificInferenceMany(InferenceRule::EQUALITY_PROXY_REPLACEMENT, prems));
  }
  // TODO isn't this done atomatically
  res->setAge(cl->age()); // MS: this seems useless; as long as EqualityProxy is only operating as a part of preprocessing, age is going to 0 anyway

  return res;
} // EqualityProxy::apply(Clause*)

/**
 * If @b lit literal is not an equality literal, return it. Otherwise, return @b lit
 * with the equality predicatce replaced by the equality proxy predicate for the same
 * sort as the equality predicate.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
Literal* EqualityProxyMono::apply(Literal* lit)
{
  if (!lit->isEquality()) {
    return lit;
  }

  TermList sort = SortHelper::getEqualityArgumentSort(lit);
  return makeProxyLiteral(lit->polarity(), *lit->nthArgument(0), *lit->nthArgument(1), sort);
} // EqualityProxy::apply(Literal*)

/**
 * True if the sort has a proxy predicate. Currently, this function will always return true,
 * since we do not have options allowing one to only apply equality proxy to some sorts.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
bool EqualityProxyMono::haveProxyPredicate(TermList sort) const
{
  return s_proxyPredicates.find(sort);
} // haveProxyPredicate

/**
 * If the equality proxy predicate for this sort was already created, return it.
 * Otherwise, create and return it. When the symbol is created, introduce a new predicate
 * definition E(x,y) <=> x = y and save it in the array s_proxyPremises.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
unsigned EqualityProxyMono::getProxyPredicate(TermList sort)
{
  unsigned pred;
  if (s_proxyPredicates.find(sort, pred)) {
    return pred;
  }

  unsigned newPred = env.signature->addFreshPredicate(2,"sQ","eqProxy");
  Signature::Symbol* predSym = env.signature->getPredicate(newPred);
  OperatorType* predType = OperatorType::getPredicateType({sort, sort});
  predSym->setType(predType);
  predSym->markEqualityProxy();
  // don't need congruence axioms for the equality predicate itself
  predSym->markSkipCongruence();

  ASS(sort.isTerm());
  ASS(sort.term()->shared());
  ASS(sort.term()->ground());

  ALWAYS(s_proxyPredicates.insert(sort,newPred));
  s_proxyPredicateSorts.insert(newPred,sort);

  Literal* proxyLit = Literal::create2(newPred,true,TermList(0,false),TermList(1,false));
  Literal* eqLit = Literal::createEquality(true,TermList(0,false),TermList(1,false),sort);
  Formula* defForm = new BinaryFormula(IFF, new AtomicFormula(proxyLit), new AtomicFormula(eqLit));
  Formula* quantDefForm = Formula::quantify(defForm);

  FormulaUnit* defUnit = new FormulaUnit(quantDefForm,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_PROXY_AXIOM1));

  s_proxyPremises.insert(sort, defUnit);
  InferenceStore::instance()->recordIntroducedSymbol(defUnit, SymbolType::PRED, newPred);
  return newPred;
}

/**
 * Create an equality proxy axiom clause (for example, reflexivity, symmetry
 * or transitivity) and return it. 
 * @author Andrei Voronkov @since
 * 16/05/2014 Manchester
 */
Clause* EqualityProxyMono::createEqProxyAxiom(const LiteralStack& literalStack)
{
  DHSet<TermList> sorts;
  UnitList* prems = 0;

  LiteralStack::ConstIterator it(literalStack);
  while (it.hasNext()) {
    Literal* l = it.next();
    TermList srt;
    if (!s_proxyPredicateSorts.find(l->functor(),srt)) {
      continue;
    }
    if (!sorts.insert(srt)) {
      continue;
    }
    Unit* prem = s_proxyPremises.get(srt);
    ASS(prem);
    UnitList::push(prem, prems);
  }
  ASS(prems);
  Clause* res = Clause::fromStack(literalStack,NonspecificInferenceMany(InferenceRule::EQUALITY_PROXY_AXIOM2,prems));
  return res;
} // EqualityProxy::createEqProxyAxiom

/**
 * Create the equality proxy literal (not) E(erg0,arg1) for a given sort.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
Literal* EqualityProxyMono::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort)
{
  unsigned pred = getProxyPredicate(sort);
  TermList args[] = {arg0, arg1};
  return Literal::create(pred, 2, polarity, args);
} // EqualityProxy::makeProxyLiteral

