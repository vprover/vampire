
/*
 * File BFNT.cpp.
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
 * @file BFNT.hpp
 * Implements class BFNT used to implement the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Array.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"

#include "Property.hpp"
#include "BFNT.hpp"

#define BNFT_SHOW_TRANSFORMED 1
// uncomment this to show the generated problem in TPTP
#define BNFT_TPTP_TRANSFORMED 0

#if BNFT_TPTP_TRANSFORMED
#include "Shell/TPTP.hpp"
#endif

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;

/**
 * Create a new transformer and save the equality proxy predicate
 * as _proxy.
 * @since 30/07/2011 Manchester
 */
BFNT::BFNT(Property* prop)
 // : _property(prop) // MS: unused
{
  _proxy = env.signature->addFreshPredicate(2,"equalish");
}

/**
 * Apply the BFNT transformation to a collection of clauses. The resulting flat
 * clauses will be saved in the stack _flat.
 * @since 30/07/2011 Manchester
 */
void BFNT::apply(UnitList* units)
{
  CALL("BFNT::apply(UnitList*&)");

  // create equality proxy symbol
  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    _flat.push(apply(cl));
#if BNFT_SHOW_TRANSFORMED
    cout << "Flat: " << _flat.top()->toString() << "\n";
#endif
#if BNFT_TPTP_TRANSFORMED
    cout << "%\n% " << cl->toString() << "\n%\n";
    cout << TPTP::toString(_flat.top()) << "\n";
#endif   
  }
} // BFNT::apply

/**
 * Apply the transformation to a clause and return the result.
 * If the clause if flat, the clause itself will be returned.
 * @since 30/07/2011 Manchester
 */
Clause* BFNT::apply(Clause* cl)
{
  CALL("BFNT::apply(Clause*)");

  // first, get rid of negative inequalities x != y among variables
  cl = resolveNegativeVariableEqualities(cl);

  // new, find the maximal variable number
  int maxVar = -1;
  VirtualIterator<unsigned> varIt = cl->getVariableIterator();
  while (varIt.hasNext()) {
    int var = varIt.next();
    if (var > maxVar) {
      maxVar = var;
    }
  }
  // here we reuse literals denoting the same (non-variable) subterms
  Map<Term*,Literal*> _literalMap;
  Map<Term*,unsigned> _variableMap;
  // move all literals to a stack
  Stack<Literal*> lits;
  for (int i = cl->length()-1; i>=0; i--) {
    lits.push((*cl)[i]);
  }
  // process literals one by one and save them in the stack result
  Stack<Literal*> result;
  bool updated = false; // will be false if all literals were already flat
  while (!lits.isEmpty()) {
    Literal* lit = lits.pop();
    if (!lit->isEquality()) {
      bool modified = false;
      Stack<TermList> args;
      for (TermList* ts = lit->args();ts->isNonEmpty();ts = ts->next()) {
	if (ts->isVar()) {
	  args.push(*ts);
	  continue;
	}
	// ts is not a variable
	// if it is a constant and the problem has no equality, keep it as it is
	// if (!_property->equalityAtoms() && ts->term()->arity() == 0) {
	//   bool added;
	//   _problemConstants.add(ts->term(),added);
	//   if (added) {
	//     _constants.push(ts->term());
	//   }
	//   args.push(*ts);
	//   continue;
	// }
	// otherwise, flatten it
	modified = true;
	TermList newVar;
	newVar.makeVar(++maxVar);
	args.push(newVar);
	// create an inequality ts != newVar and save it to lits
	lits.push(Literal::createEquality(false,*ts,newVar, SortHelper::getResultSort(ts->term())));
      }
      if (!modified) { // literal was already flat
	result.push(lit);
	continue;
      }
      updated = true;
      // literal was non-flat, add its flat version
      result.push(Literal::create(lit,args.begin()));
      continue;
    }
    // lit is equality
    unsigned litArgSort = SortHelper::getEqualityArgumentSort(lit);
    updated = true;
    TermList* lhs = lit->nthArgument(0);
    TermList* rhs = lit->nthArgument(1);
    if (!lit->polarity()) { // lhs != rhs
      if (lhs->isVar()) { // x = rhs, swap lhs and rhs
	ASS(!rhs->isVar());
	TermList* tmp = lhs;
	lhs = rhs;
	rhs = tmp;
      }
      else if (!rhs->isVar()) { // lhs != rhs, both lhs and rhs are non-variables
	// make it rhs != x \/ lhs != x
	TermList v1;
	v1.makeVar(++maxVar);
	// save lhs != v1
	lits.push(Literal::createEquality(false, *lhs, v1, litArgSort));
	// save rhs != v1
	lits.push(Literal::createEquality(false, *rhs, v1, litArgSort));
	continue;
      }
      // Now lhs != x
      // flatten lhs
      Term* l = lhs->term();
      Stack<TermList> args;
      for (TermList* ts = l->args();ts->isNonEmpty();ts = ts->next()) {
	if (ts->isVar()) {
	  args.push(*ts);
	  continue;
	}
	// ts is not a variable, flatten it
	TermList newVar;
	newVar.makeVar(++maxVar);
	args.push(newVar);
	// create an inequality ts != newVar and save it to lits
	lits.push(Literal::createEquality(false,*ts,newVar, SortHelper::getResultSort(ts->term())));
	continue;
      }
      // args contains only variables
      args.push(*rhs);
      unsigned f = l->functor();
      // find the predicate p corresponding to f
      unsigned p; 
      if (!_preds.find(f,p)) { // no such symbol
	vstring pname = env.signature->getFunction(f)->name();
	p = env.signature->addFreshPredicate(args.length(),pname.c_str());
	_preds.insert(f,p);
      }
      // create the new flat literal and save it
      result.push(Literal::create(p,args.length(),false,false,args.begin()));
      continue;
    }
    // positive equation lhs = rhs
    TermList v1;
    TermList v2;
    if (lhs->isVar()) {
      v1 = *lhs;
    }
    else {
      // save lhs != v1
      v1.makeVar(++maxVar);
      lits.push(Literal::createEquality(false,*lhs,v1,litArgSort));
    }
    if (rhs->isVar()) {
      v2 = *rhs;
    }
    else {
      // save rhs != v2
      v2.makeVar(++maxVar);
      lits.push(Literal::createEquality(false,*rhs,v2,litArgSort));
    }
    // save v1 = v2
    result.push(Literal::create2(_proxy,true,v1,v2));
  }
  return updated ? Clause::fromStack(result, NonspecificInference1(InferenceRule::BFNT_FLATTENING,cl))
                  : cl;
} // BFNT::apply

/**
 * Apply equality resolution to all negative equalities between variables
 * in cl and return the result. If cl contains no such inequalities, return cl
 * itself.
 * @since 30/07/2011 Manchester
 */
Clause* BFNT::resolveNegativeVariableEqualities(Clause* cl)
{
  CALL("BFNT::resolveNegativeVariableEqualities");

  Array<Literal*> lits;
  Stack<Literal*> inequalities;
  int n = 0;
  for (unsigned i = 0;i < cl->length();i++) {
    Literal* lit = (*cl)[i];
    if (lit->isEquality() &&
	lit->isNegative() &&
	lit->nthArgument(0)->isVar() &&
	lit->nthArgument(1)->isVar()) {
      inequalities.push(lit);
    }
    else {
      lits[n++] = lit;
    }
  }
  if (inequalities.isEmpty()) {
    return cl;
  }
  bool diffVar = false;
  while (!inequalities.isEmpty()) {
    Literal* ineq = inequalities.pop();
    unsigned v1 = ineq->nthArgument(0)->var();
    TermList* v2 = ineq->nthArgument(1);
    if (v1 == v2->var()) { // x != x
      continue;
    }
    diffVar = true;
    Substitution subst;
    subst.bind(v1,*v2);
    cl = new(n) Clause(n,NonspecificInference1(InferenceRule::EQUALITY_RESOLUTION,cl));
    for (int i = n-1;i >= 0;i--) {
      Literal* lit = SubstHelper::apply<Substitution>(lits[i],subst);
      (*cl)[i] = lit;
      lits[i] = lit;
    }
  }
  if (!diffVar) { // only X != X found, we should still perform the inference
    cl = new(n) Clause(n,NonspecificInference1(InferenceRule::EQUALITY_RESOLUTION,cl));
    for (int i = n-1;i >= 0;i--) {
      (*cl)[i] = lits[i];
    }
  }
#if BNFT_SHOW_TRANSFORMED
  cout << "EqRes: " << cl->toString() << "\n";
#endif
  return cl;
} // BFNT::resolveNegativeVariableEqualities

Problem* BFNT::createProblem(unsigned modelSize)
{
  CALL("BFNT::createProblem");

  UnitList* units = create(modelSize);
  Problem* res = new Problem(units);
  return res;
}

/**
 * Create the list of clauses for a finite domain of some size. Return all the collected
 * flat clauses plus the distinct constant and totality axoms.
 * @since 30/07/2011 Manchester
 */
UnitList* BFNT::create(unsigned modelSize)
{
  CALL("BFNT::create");
  ASS(modelSize > 0);

  unsigned len = _constants.length();
  while (len < modelSize) {
    _constants.push(Term::createConstant(Int::toString(++len)));
  }
  UnitList* result = 0;

  // create inequalities between constants
  Term** cs = _constants.begin();
  for (unsigned i = 0;i < len;i++) {
    TermList c1(cs[i]);
    for (unsigned j = 0;j < len;j++) {
      if (i == j) continue;
      TermList c2(cs[j]);
      // create c1 != c2
      Clause* cls = new(1) Clause(1,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::BFNT_DISTINCT));
      (*cls)[0] = Literal::create2(_proxy,false,c1,c2);
#if BNFT_SHOW_TRANSFORMED
      cout << "EqProxy: " << cls->toString() << "\n";
#endif
#if BNFT_TPTP_TRANSFORMED
      cout << TPTP::toString(cls) << "\n";
#endif
      result = new UnitList(cls,result);
    }
  }

  // create totality axioms
  Map<unsigned,unsigned>::Iterator preds(_preds);
  unsigned fun;
  unsigned pred;
  unsigned constantsFound=0; // the number of constants, used for symmetry breaking
  while (preds.hasNext()) {
    preds.next(fun,pred);
    int arity = env.signature->getPredicate(pred)->arity();
    Stack<TermList> args;
    for (int i = 0;i < arity;i++) {
      TermList v;
      v.makeVar(i);
      args.push(v);
    }
    Stack<Literal*> lits;
    unsigned elements = modelSize;
    if (arity == 1) {
      constantsFound++;
      if (constantsFound < modelSize) {
	elements = constantsFound;
      }
    }
    for (unsigned i = 0;i < elements;i++) {
      TermList con(cs[i]);
      args.pop();
      args.push(con);
      lits.push(Literal::create(pred,arity,true,false,args.begin()));
    }
    result = new UnitList(Clause::fromStack(lits,
					    NonspecificInference0(UnitInputType::AXIOM,InferenceRule::BFNT_TOTALITY)),
			  result);
#if BNFT_TPTP_TRANSFORMED
    cout << TPTP::toString(result->head()) << "\n";
#endif
#if BNFT_SHOW_TRANSFORMED
    cout << "Tot: " << result->head()->toString() << "\n";
#endif
  }
  Stack<Clause*>::Iterator sit(_flat);
  while (sit.hasNext()) {
    result = new UnitList(sit.next(),result);
  }
  return result;
} // BFNT::create
