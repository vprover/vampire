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

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "EqualityProxy.hpp"

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;

/**
 * Constructor, simply memorizes the value of the equality proxy option
 * and which of the two variants of the transformation to run.
 */
EqualityProxy::EqualityProxy(Options::EqualityProxy opt, bool poly)
: _opt(opt), _poly(poly), _proxyPredicate(0), _defUnit(nullptr)
{
  ASS(opt != Options::EqualityProxy::OFF);
} // EqualityProxy::EqualityProxy

/**
 * Apply the equality proxy transformation to a problem. The problem must only contain
 * clauses, no formulas.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxy::apply(Problem& prb)
{
  bool hadEquality = prb.hasEquality();

  apply(prb.units());
  prb.invalidateByRemoval();
  prb.reportEqualityEliminated();
  if (_poly && _defUnit) {
    // the single proxy predicate carries a type argument
    prb.reportPolymorphicSymAdded();
  }

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
void EqualityProxy::apply(UnitList*& units)
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
 * Add reflexivity, symmetry and transitivity axioms for the proxy predicate of
 * the given sort, depending on the value of the equality proxy option.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxy::addLocalAxioms(UnitList*& units, TermList sort)
{
  // in the polymorphic case, variable 0 is the sort variable, so the terms start at 1
  unsigned v0 = _poly ? 1 : 0;

  // reflexivity
  Stack<Literal*> lits;
  lits.push(makeProxyLiteral(true,TermList(v0,false),TermList(v0,false), sort));
  UnitList::push(createEqProxyAxiom(lits),units);

  // symmetry
  if (_opt == Options::EqualityProxy::RS || _opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(v0,false),TermList(v0+1,false), sort));
    lits.push(makeProxyLiteral(true,TermList(v0+1,false),TermList(v0,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
  // transitivity
  if (_opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(v0,false),TermList(v0+1,false), sort));
    lits.push(makeProxyLiteral(false,TermList(v0+1,false),TermList(v0+2,false), sort));
    lits.push(makeProxyLiteral(true,TermList(v0,false),TermList(v0+2,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
} // EqualityProxy::addLocalAxioms

/**
 * Add axioms for the equality proxy predicates
 *
 * In the monomorphic case we add axioms only for the sorts for which the equality proxy
 * predicates were created. Therefore this function should be called only after the equality
 * proxy replacement is performed on the whole problem, so that the needed equality proxy
 * predicates are created at this time.
 */
void EqualityProxy::addAxioms(UnitList*& units)
{
  // if we're adding congruence axioms, we need to add them before adding the local axioms.
  // Local axioms are added only for sorts on which equality is used, and the congruence axioms
  // may spread the equality use into new sorts
  if (_opt == Options::EqualityProxy::RSTC) {
    addCongruenceAxioms(units);
  }

  if (_poly) {
    addLocalAxioms(units, TermList(0,false));
  } else {
    decltype(_proxyPredicates)::Iterator it(_proxyPredicates);
    while(it.hasNext()) {
      addLocalAxioms(units, it.nextKey());
    }
  }
} // addAxioms

/**
 * Prepare the arguments of the two sides of a congruence axiom, along with the
 * equality proxy literals relating them.
 *
 * symbolType is the type of symbol for whose arguments we're generating the
 * equalities.
 */
bool EqualityProxy::getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2, OperatorType* symbolType, bool skipSortsWithoutEquality)
{
  ASS_EQ(cnt, symbolType->arity());

  lits.reset();
  vars1.reset();
  vars2.reset();

  static Substitution localSubst;
  localSubst.reset();

  for (unsigned i=0; i<cnt; i++) {
    TermList v1(2*i, false);
    TermList v2(2*i+1, false);
    TermList sort = symbolType->arg(i);
    if (sort == AtomicSort::superSort()) {
      // a type argument: it must be the same on both sides, and the sorts of the
      // remaining arguments need to be instantiated accordingly
      ASS(_poly);
      TermList var = symbolType->quantifiedVar(i);
      localSubst.bindUnbound(var.var(), v1);
      vars1.push(v1);
      vars2.push(v1);
      continue;
    }
    if (_poly) {
      sort = SubstHelper::apply(sort, localSubst);
    }
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
void EqualityProxy::addCongruenceAxioms(UnitList*& units)
{
  // This is Krystof Hoder's comment:
  // TODO: skip UPDR predicates!!!
  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;
  TermList srt;

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
    ALWAYS(SortHelper::tryGetResultSort(t1, srt));
    lits.push(makeProxyLiteral(true, TermList(t1), TermList(t2), srt));

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
    // with a single polymorphic proxy predicate every sort has one, so nothing gets skipped there
    bool skipSortsWithoutEquality = !_poly;
    bool haveEqualities = getArgumentEqualityLiterals(arity, lits, vars1, vars2, predSym->predType(), skipSortsWithoutEquality);
    if (skipSortsWithoutEquality && !haveEqualities) {
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
Clause* EqualityProxy::apply(Clause* cl)
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
      // in the polymorphic case there is a single definition, so record it only once
      if (!_poly || proxyPremises.isEmpty()) {
        Unit* prem = premiseFor(rlit);
        ASS(prem);
        proxyPremises.push(prem);
      }
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
  // TODO isn't this done automatically
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
Literal* EqualityProxy::apply(Literal* lit)
{
  if (!lit->isEquality()) {
    return lit;
  }

  TermList sort = SortHelper::getEqualityArgumentSort(lit);
  return makeProxyLiteral(lit->polarity(), *lit->nthArgument(0), *lit->nthArgument(1), sort);
} // EqualityProxy::apply(Literal*)

/**
 * True if the sort has a proxy predicate. In the polymorphic case a single proxy predicate
 * serves all the sorts, so it is enough that it has already been created.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
bool EqualityProxy::haveProxyPredicate(TermList sort) const
{
  if (_poly) {
    return _defUnit != nullptr;
  }
  return _proxyPredicates.find(sort);
} // haveProxyPredicate

/**
 * If the equality proxy predicate for this sort was already created, return it.
 * Otherwise, create and return it. When the symbol is created, introduce a new predicate
 * definition E(x,y) <=> x = y and remember it as the premise of the introduction.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 * @since 23/10/2020 Leicester
 */
unsigned EqualityProxy::getProxyPredicate(TermList sort)
{
  if (_poly) {
    if (_defUnit) {
      return _proxyPredicate;
    }
    // the single proxy predicate is polymorphic: E : !>[X]:(X*X) > $o
    sort = TermList(0,false);
  } else {
    unsigned pred;
    if (_proxyPredicates.find(sort, pred)) {
      return pred;
    }
    ASS(sort.isTerm());
    ASS(sort.term()->shared());
    ASS(sort.term()->ground());
  }

  unsigned newPred = env.signature->addFreshPredicate(_poly ? 3 : 2,"sQ","eqProxy");
  Signature::Symbol* predSym = env.signature->getPredicate(newPred);
  OperatorType* predType = OperatorType::getPredicateType({sort, sort}, _poly ? 1 : 0);
  predSym->setType(predType);
  predSym->markEqualityProxy();
  // don't need congruence axioms for the equality predicate itself
  predSym->markSkipCongruence();

  TermList var1 = TermList(_poly ? 1 : 0,false);
  TermList var2 = TermList(_poly ? 2 : 1,false);

  Literal* proxyLit;
  if (_poly) {
    TermList args[] = {sort, var1, var2};
    proxyLit = Literal::create(newPred, 3, true, args);
  } else {
    proxyLit = Literal::create2(newPred,true,var1,var2);
  }
  Literal* eqLit = Literal::createEquality(true,var1,var2,sort);
  Formula* defForm = new BinaryFormula(IFF, new AtomicFormula(proxyLit), new AtomicFormula(eqLit));
  Formula* quantDefForm = Formula::quantify(defForm);

  FormulaUnit* defUnit = new FormulaUnit(quantDefForm,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_PROXY_DEFINITION));

  if (_poly) {
    _proxyPredicate = newPred;
    _defUnit = defUnit;
  } else {
    ALWAYS(_proxyPredicates.insert(sort,newPred));
    _proxyPredicateSorts.insert(newPred,sort);
    _proxyPremises.insert(sort, defUnit);
  }

  InferenceStore::instance()->recordIntroducedSymbol(defUnit, predSym);
  return newPred;
}

/**
 * Return the definition the given equality proxy literal came from,
 * or 0 if the literal is not an equality proxy one.
 */
Unit* EqualityProxy::premiseFor(Literal* proxyLit) const
{
  if (_poly) {
    return (_defUnit && proxyLit->functor() == _proxyPredicate) ? _defUnit : 0;
  }
  TermList srt;
  if (!_proxyPredicateSorts.find(proxyLit->functor(),srt)) {
    return 0;
  }
  return _proxyPremises.get(srt);
} // EqualityProxy::premiseFor

/**
 * Create an equality proxy axiom clause (for example, reflexivity, symmetry
 * or transitivity) and return it.
 * @author Andrei Voronkov @since
 * 16/05/2014 Manchester
 * @since 23/10/2020 Leicester
 */
Clause* EqualityProxy::createEqProxyAxiom(const LiteralStack& literalStack)
{
  if (_poly) {
    ASS(_defUnit);
    return Clause::fromStack(literalStack, NonspecificInference1(InferenceRule::EQUALITY_PROXY_AXIOM,_defUnit));
  }

  DHSet<Unit*> seen;
  UnitList* prems = 0;

  LiteralStack::ConstIterator it(literalStack);
  while (it.hasNext()) {
    Unit* prem = premiseFor(it.next());
    if (!prem || !seen.insert(prem)) {
      continue;
    }
    UnitList::push(prem, prems);
  }
  ASS(prems);
  Clause* res = Clause::fromStack(literalStack,NonspecificInferenceMany(InferenceRule::EQUALITY_PROXY_AXIOM,prems));
  return res;
} // EqualityProxy::createEqProxyAxiom

/**
 * Create the equality proxy literal (not) E(arg0,arg1) for a given sort.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 * @since 23/10/2020 Leicester
 */
Literal* EqualityProxy::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort)
{
  unsigned pred = getProxyPredicate(sort);
  if (_poly) {
    TermList args[] = {sort, arg0, arg1};
    return Literal::create(pred, 3, polarity, args);
  }
  TermList args[] = {arg0, arg1};
  return Literal::create(pred, 2, polarity, args);
} // EqualityProxy::makeProxyLiteral
