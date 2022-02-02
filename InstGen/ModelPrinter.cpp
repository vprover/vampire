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
 * @file ModelPrinter.cpp
 * Implements class ModelPrinter.
 */

#include <algorithm>

#include "ModelPrinter.hpp"

#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/GroundingIndex.hpp"

#include "Shell/PredicateDefinition.hpp"

#include "IGAlgorithm.hpp"

namespace InstGen
{

using namespace Shell;

ModelPrinter::ModelPrinter(IGAlgorithm& iga)
 : _iga(iga)
{
  CALL("ModelPrinter::ModelPrinter");
}

bool ModelPrinter::haveNonDefaultSorts()
{
  CALL("ModelPrinter::haveNonDefaultSorts");

  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    OperatorType* type = env.signature->getFunction(i)->fnType();
    if(!type->isAllDefault()) { return false; }
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    OperatorType* type = env.signature->getPredicate(i)->predType();
    if(!type->isAllDefault()) { return false; }
  }
  return true;
}

bool ModelPrinter::isEprProblem()
{
  CALL("ModelPrinter::isEprProblem");

  unsigned funCnt = env.signature->functions();
  for(unsigned i=0; i<funCnt; i++) {
    if(env.signature->functionArity(i)>0) {
      return false;
    }
  }
  return true;
}

bool ModelPrinter::tryOutput(ostream& stm)
{
  CALL("ModelPrinter::tryOutput");

  if(!isEprProblem() || !haveNonDefaultSorts()) {
    return false;
  }

  Stack<TermList> args;
  Problem::TrivialPredicateMap::Iterator removedPreds(_iga.getProblem().trivialPredicates());
  while(removedPreds.hasNext()) {
    unsigned pred;
    bool assignment;
    removedPreds.next(pred, assignment);
    ASS_NEQ(pred,0);
    unsigned arity = env.signature->predicateArity(pred);
    args.reset();
    for(unsigned i=0; i<arity; i++) {
      args.push(TermList(i, false));
    }
    Literal* lit = Literal::create(pred, arity, assignment, false, args.begin());
    _trueLits.push(lit);
  }

  collectTrueLits();
  //TODO fix the below AYB
  if(env.signature->functions()!=0) {
    if(_usedConstants.isEmpty()) {
      unsigned newFunc = env.signature->addFreshFunction(0,"c");
      TermList newConstTrm(Term::create(newFunc, 0, 0));
      _usedConstants.push(newConstTrm);
      _usedConstantSet.insert(newFunc);
    }
    analyzeEqualityAndPopulateDomain();
    rewriteLits(_trueLits);

    outputDomainSpec(stm);
    outputFunInterpretations(stm);
  }
  outputPredInterpretations(stm);

  return true;
}

bool ModelPrinter::isEquality(Literal* lit)
{
  CALL("ModelPrinter::isEquality");

  return lit->isEquality() || env.signature->getPredicate(lit->functor())->equalityProxy();
}

/**
 * Collect constants used in @c lit into _usedConstantSet and _usedConstants.
 *
 * Function assumes there are no non-constant functions.
 */
void ModelPrinter::collectConstants(Literal* lit)
{
  CALL("ModelPrinter::collectConstants");

  SubtermIterator sti(lit);
  while(sti.hasNext()) {
    TermList t = sti.next();
    if(t.isVar()) {
      continue;
    }
    Term* trm = t.term();
    ASS_EQ(trm->arity(),0);
    unsigned func = trm->functor();
    if(_usedConstantSet.insert(func)) {
      _usedConstants.push(t);
    }
  }
}

void ModelPrinter::collectTrueLits()
{
  CALL("ModelPrinter::collectTrueLits");

  ClauseIterator ait = _iga.getActive();
  while(ait.hasNext()) {
    Clause* cl = ait.next();
    unsigned selCnt = cl->numSelected();
    ASS_G(selCnt, 0);
    for(unsigned i=0; i<selCnt; i++) {
      Literal* lit = (*cl)[i];
      collectConstants(lit);
      if(isEquality(lit)) {
	_trueEqs.push(lit);
      }
      else {
	_trueLits.push(lit);
      }
    }
  }
}

/**
 * Comparator that ensures instances go before more general clauses in the ordering
 */
struct ModelPrinter::InstLitComparator
{
  bool operator()(Literal* l1, Literal* l2)
  {
    if(l1->functor()!=l2->functor()) {
      return l1->functor()<l2->functor();
    }
    if(l1->weight()!=l2->weight()) {
      return l1->weight()>l2->weight();
    }
    return l1->getDistinctVars()<l2->getDistinctVars();
  }
};

void ModelPrinter::generateNewInstances(Literal* base, TermStack& domain, DHSet<Literal*>& instSet, LiteralStack& instAcc)
{
  CALL("ModelPrinter::generateNewInstances");

  //TODO: Add a smarted way of handling variables occurring multiple times!!! (now it's by MatchingUtils::match)

  unsigned arity = base->arity();
  unsigned domSz= domain.size();

  static DArray<TermList> args;
  static DArray<bool> variables;
  static DArray<unsigned> nextIndexes;
  OperatorType* predType = env.signature->getPredicate(base->functor())->predType();

  args.ensure(arity);
  variables.ensure(arity);
  nextIndexes.ensure(arity);

  for(unsigned i=0; i<arity; i++) {
    TermList baseArg = *base->nthArgument(i);
    bool isVar = baseArg.isVar();
    variables[i] = isVar;
    if(isVar) {
      nextIndexes[i] = 0;
    }
    else {
      args[i] = baseArg;
    }
  }

  unsigned depth = 0;
  for(;;) {
    while(depth<arity && !variables[depth]) {
      depth++;
    }
    bool goingDown;
    if(depth==arity) {
      //now we can generate a literal
      Literal* inst;
      if(base->isEquality()) {
	ASS(args[0].isTerm());
	inst = Literal::createEquality(base->isPositive(), args[0], args[1], SortHelper::getResultSort(args[0].term()));
      }
      else {
	inst = Literal::create(base, args.array());
      }
      bool shouldAdd = !instSet.contains(inst);
      if(shouldAdd) {
	Literal* opInst = Literal::complementaryLiteral(inst);
	shouldAdd = !instSet.contains(opInst);
      }
      if(shouldAdd) {
	shouldAdd = MatchingUtils::match(base, inst, false);
      }
      if(shouldAdd) {
	instSet.insert(inst);
	instAcc.push(inst);
      }

      goingDown = true;
    }
    else {
      TermList arg;
      do {
        if(nextIndexes[depth]==domSz) {
	  nextIndexes[depth] = 0;

	  goingDown = true;
	  goto done_with_level;
        }
        arg = domain[nextIndexes[depth]];
        nextIndexes[depth]++;
      } while(SortHelper::getResultSort(arg.term())!=predType->arg(depth));
      args[depth] = arg;
      goingDown = false;
    }

  done_with_level:
    if(goingDown) {
      do {
	if(depth==0) {
	  //we're done
	  return;
	}
	depth--;
      } while(!variables[depth]);
    }
    else {
      depth++;
    }
  }
}

void ModelPrinter::getInstances(LiteralStack& trueLits, TermStack& domain, LiteralStack& instanceAcc)
{
  CALL("ModelPrinter::getInstances");

  static DHSet<Literal*> instSet;
  instSet.reset();

  std::sort(trueLits.begin(), trueLits.end(), InstLitComparator());
  LiteralStack::BottomFirstIterator tlIt(trueLits);
  while(tlIt.hasNext()) {
    Literal* lit = tlIt.next();
    generateNewInstances(lit, domain, instSet, instanceAcc);
  }
}

void ModelPrinter::analyzeEqualityAndPopulateDomain()
{
  CALL("ModelPrinter::analyzeEqualityAndPopulateDomain");

  TermStack eqInstDomain = _usedConstants;
  LiteralStack eqInsts;
  getInstances(_trueEqs, eqInstDomain, eqInsts);

  unsigned funCnt = env.signature->functions();
  IntUnionFind uif(funCnt);

  LiteralStack::Iterator eqit(eqInsts);
  while(eqit.hasNext()) {
    Literal* lit = eqit.next();
    if(!lit->isPositive()) {
      continue;
    }
    TermList arg1 = *lit->nthArgument(0);
    TermList arg2 = *lit->nthArgument(1);
    ASS(arg1.isTerm());
    ASS(arg2.isTerm());
    unsigned fun1 = arg1.term()->functor();
    unsigned fun2 = arg2.term()->functor();
    uif.doUnion(fun1, fun2);
  }

  uif.evalComponents();
  IntUnionFind::ComponentIterator eqClassIt(uif);
  while(eqClassIt.hasNext()) {
    IntUnionFind::ElementIterator ecElIt = eqClassIt.next();

    ALWAYS(ecElIt.hasNext());
    unsigned firstFunc = ecElIt.next();

    if(!_usedConstantSet.contains(firstFunc)) {
      ASS(!ecElIt.hasNext()); //constant that is not used is alone in its equivalence class
      continue;
    }
    TermList firstTerm = TermList(Term::create(firstFunc, 0, 0));
    vstring firstTermStr = firstTerm.toString();
    TermList eqClassSort = SortHelper::getResultSort(firstTerm.term());
    unsigned reprFunc = env.signature->addStringConstant(firstTermStr);
    OperatorType* reprType = OperatorType::getConstantsType(eqClassSort);
    env.signature->getFunction(reprFunc)->setType(reprType);
    TermList reprTerm = TermList(Term::create(reprFunc, 0, 0));
    _rewrites.insert(firstTerm, reprTerm);

    _domain.push(reprTerm);

    while(ecElIt.hasNext()) {
      unsigned elFunc = ecElIt.next();
      TermList elTerm = TermList(Term::create(elFunc, 0, 0));
      ASS_EQ(eqClassSort, SortHelper::getResultSort(elTerm.term()));
      _rewrites.insert(elTerm, reprTerm);
    }
  }
}

void ModelPrinter::rewriteLits(LiteralStack& lits)
{
  CALL("ModelPrinter::rewriteLits");

  static TermStack args;

  LiteralStack::Iterator iter(lits);
  while(iter.hasNext()) {
    Literal* lit = iter.next();
    ASS(!isEquality(lit)); //we don't have equalities anymore at the point where this function is called
    unsigned arity = lit->arity();
    args.reset();
    bool modified = false;
    for(unsigned i=0; i<arity; i++) {
      TermList origArg = *lit->nthArgument(i);
      TermList tgt;
      if(origArg.isTerm() && _rewrites.find(origArg, tgt)) {
	args.push(tgt);
	modified = true;
      }
      else {
	args.push(origArg);
      }
    }
    ASS_EQ(args.size(), arity);
    if(!modified) {
      continue;
    }
    Literal* newLit = Literal::create(lit, args.begin());
    iter.replace(newLit);
  }
}

void ModelPrinter::outputDomainSpec(ostream& out)
{
  CALL("ModelPrinter::outputDomainSpec");
  ASS(_domain.isNonEmpty());

  out << "fof(model1,interpretation_domain," << endl
      << "    ! [X] : ( ";

  TermStack::BottomFirstIterator dit(_domain);
  while(dit.hasNext()) {
    TermList dt = dit.next();
    out << "X = " << dt.toString();
    if(dit.hasNext()) {
      out << " | ";
    }
  }

  out << " ) )." << endl;
}

void ModelPrinter::outputFunInterpretations(ostream& out)
{
  CALL("ModelPrinter::outputFunInterpretations");

  if(_rewrites.isEmpty()) { return; }

  out << "fof(model2,interpretation_terms," << endl
      << "    ( ";

  EqMap::Iterator eit(_rewrites);
  while(eit.hasNext()) {
    TermList trm, repr;
    eit.next(trm, repr);
    out << trm.toString() << " = " << repr.toString();
    if(eit.hasNext()) {
      out << " & ";
    }
  }

  out << ") )." << endl;
}


/**
 * Comparator that sorts instance literals by their predicate for the output
 */
struct ModelPrinter::PredNumComparator
{
  bool operator()(Literal* l1, Literal* l2)
  {
    return l1->functor()<l2->functor();
  }
};

void ModelPrinter::outputPredInterpretations(ostream& out)
{
  CALL("ModelPrinter::outputPredInterpretations");

  LiteralStack model;
  getInstances(_trueLits, _domain, model);

  std::sort(model.begin(), model.end(), PredNumComparator());

  if(model.isEmpty()) { return; }

  out << "fof(model3,interpretation_atoms," << endl
      << "    ( ";

  LiteralStack::BottomFirstIterator mit(model);
  while(mit.hasNext()) {
    Literal* lit = mit.next();
    out << lit->toString();
    if(mit.hasNext()) {
      out << " & " << endl << "      ";
    }
  }
  out << " ) )." << endl;
}

}















