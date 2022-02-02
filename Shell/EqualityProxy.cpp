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
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "EqualityProxy.hpp"

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;


/**
 * Constructor, simply memorizes the value of the equality proxy option.
 */
EqualityProxy::EqualityProxy(Options::EqualityProxy opt)
: _opt(opt), _addedPred(0), _defUnit(0)
{
  CALL("EqualityProxy::EqualityProxy/1");
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
  CALL("EqualityProxy::apply(Problem&)");

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
void EqualityProxy::apply(UnitList*& units)
{
  CALL("EqualityProxy::apply(UnitList*&)");

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
void EqualityProxy::addLocalAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addLocalAxioms");

  // reflexivity
  Stack<Literal*> lits;
  TermList sort = TermList(false, 0);

  lits.push(makeProxyLiteral(true,TermList(1,false),TermList(1,false), sort));
  UnitList::push(createEqProxyAxiom(lits),units);

  // symmetry
  if (_opt == Options::EqualityProxy::RS || _opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(1,false),TermList(2,false), sort));
    lits.push(makeProxyLiteral(true,TermList(2,false),TermList(1,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
  // transitivity
  if (_opt == Options::EqualityProxy::RST || _opt == Options::EqualityProxy::RSTC) {
    lits.reset();
    lits.push(makeProxyLiteral(false,TermList(1,false),TermList(2,false), sort));
    lits.push(makeProxyLiteral(false,TermList(2,false),TermList(3,false), sort));
    lits.push(makeProxyLiteral(true,TermList(1,false),TermList(3,false), sort));
    UnitList::push(createEqProxyAxiom(lits),units);
  }
} // EqualityProxy::addLocalAxioms

/**
 * Add axioms for the equality proxy predicates
 */
void EqualityProxy::addAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addAxioms");

  if (_opt == Options::EqualityProxy::RSTC) {
    addCongruenceAxioms(units);
  }

  addLocalAxioms(units);

} // addAxioms

/**
 *
 * symbolType is the type of symbol for whose arguments we're generating the
 * equalities.
 */
void EqualityProxy::getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits,
    Stack<TermList>& vars1, Stack<TermList>& vars2, OperatorType* symbolType)
{
  CALL("EqualityProxy::getArgumentEqualityLiterals");
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
    if(sort != AtomicSort::superSort()){
      lits.push(makeProxyLiteral(false, v1, v2, SubstHelper::apply(sort, localSubst)));
      vars1.push(v1);
      vars2.push(v2);
    } else {
      TermList var = symbolType->quantifiedVar(i);
      localSubst.bind(var.var(), v1);
      vars1.push(v1);
      vars2.push(v1);
    }
  }
}

/**
 * For every symbol occurring in env.signature, add to the units equality congruence axioms
 * for this symbol.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
void EqualityProxy::addCongruenceAxioms(UnitList*& units)
{
  CALL("EqualityProxy::addCongruenceAxioms");

  // This is Krystof Hoder's comment:
  // TODO: skip UPDR predicates!!!
  Stack<TermList> vars1;
  Stack<TermList> vars2;
  LiteralStack lits;
  TermList srt;

  unsigned funs = env.signature->functions();
  for (unsigned i=0; i<funs; i++) {
    Signature::Symbol* fnSym = env.signature->getFunction(i);
    unsigned arity = fnSym->arity();
    OperatorType* fnType = fnSym->fnType();
    if (arity == 0) {
      continue;
    }
    getArgumentEqualityLiterals(arity, lits, vars1, vars2, fnType);
    Term* t1 = Term::create(i, arity, vars1.begin());
    Term* t2 = Term::create(i, arity, vars2.begin());
    SortHelper::tryGetResultSort(t1, srt);
    lits.push(makeProxyLiteral(true, TermList(t1), TermList(t2), srt));

    Clause* cl = createEqProxyAxiom(lits);
    UnitList::push(cl,units);
  }

  unsigned preds = env.signature->predicates();
  for (unsigned i = 1; i < preds; i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    unsigned arity = predSym->arity();
    if (predSym->equalityProxy() || predSym->arity() == 0) {
      continue;
    }
    getArgumentEqualityLiterals(arity, lits, vars1, vars2, predSym->predType());
    lits.push(Literal::create(i, arity, false, false, vars1.begin()));
    lits.push(Literal::create(i, arity, true, false, vars2.begin()));

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
  CALL("EqualityProxy::apply(Clause*)");

  unsigned clen = cl->length();

  Stack<Literal*> resLits(8);

  bool modified = false;
  for (unsigned i = 0; i < clen ; i++) {
    Literal* lit=(*cl)[i];
    Literal* rlit=apply(lit);
    resLits.push(rlit);
    if (rlit != lit) {
      ASS(lit->isEquality());
      modified = true;
    }
  }
  if (!modified) {
    return cl;
  }

  ASS(_defUnit);

  Clause* res = new(clen) Clause(clen, 
    NonspecificInference2(InferenceRule::EQUALITY_PROXY_REPLACEMENT, cl, _defUnit));
  res->setAge(cl->age());

  for (unsigned i=0;i<clen;i++) {
    (*res)[i] = resLits[i];
  }

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
  CALL("EqualityProxy::apply(Literal*)");

  if (!lit->isEquality()) {
    return lit;
  }

  TermList sort = SortHelper::getEqualityArgumentSort(lit);
  return makeProxyLiteral(lit->polarity(), *lit->nthArgument(0), *lit->nthArgument(1), sort);
} // EqualityProxy::apply(Literal*)


/**
 * If the equality proxy predicate was already created, return it.
 * Otherwise, create and return it. When the symbol is created, introduce a new predicate
 * definition E<\sigma>(x,y) <=> x = y
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 */
unsigned EqualityProxy::getProxyPredicate()
{
  CALL("EqualityProxy::getProxyPredicate");

  if(_addedPred){ return _proxyPredicate; }

  unsigned newPred = env.signature->addFreshPredicate(3,"sQ","eqProxy");
  
  TermList sort = TermList(0,false);
  TermList var1 = TermList(1,false);
  TermList var2 = TermList(2,false);

  Signature::Symbol* predSym = env.signature->getPredicate(newPred);
  OperatorType* predType = OperatorType::getPredicateType({sort, sort}, 1);
  predSym->setType(predType);
  predSym->markEqualityProxy();

  static TermStack args;
  args.reset();

  args.push(sort);
  args.push(var1);
  args.push(var2);

  Literal* proxyLit = Literal::create(newPred, 3, true, false, args.begin());
  Literal* eqLit = Literal::createEquality(true,var1,var2,sort);
  Formula* defForm = new BinaryFormula(IFF, new AtomicFormula(proxyLit), new AtomicFormula(eqLit));
  Formula* quantDefForm = Formula::quantify(defForm);

  _defUnit = new FormulaUnit(quantDefForm,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::EQUALITY_PROXY_AXIOM1));

  InferenceStore::instance()->recordIntroducedSymbol(_defUnit, false, newPred);
  _proxyPredicate = newPred;
  _addedPred = true;
  return newPred;
}

/**
 * Create an equality proxy axiom clause (for example, reflexivity, symmetry
 * or transitivity) and return it. 
 * @author Andrei Voronkov @since
 * 16/05/2014 Manchester
 * @since 23/10/2020 Leicester
 */
Clause* EqualityProxy::createEqProxyAxiom(const LiteralStack& literalStack)
{
  CALL("EqualityProxy::createEqProxyAxiom(const LiteralStack&,unsigned)");

  ASS(_defUnit);
  Clause* res = Clause::fromStack(literalStack, NonspecificInference1(InferenceRule::EQUALITY_PROXY_AXIOM2,_defUnit));
  return res;
} // EqualityProxy::createEqProxyAxiom

/**
 * Create the equality proxy literal (not) E<sort>(erg0,arg1) for a given sort.
 * @author Andrei Voronkov
 * @since 16/05/2014 Manchester
 * @since 23/10/2020 Leicester
 */
Literal* EqualityProxy::makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort)
{
  CALL("EqualityProxy::makeProxyLiteral");

  unsigned pred = getProxyPredicate();
  TermList args[] = {sort, arg0, arg1};
  return Literal::create(pred, 3, polarity, false, args);
} // EqualityProxy::makeProxyLiteral

