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
 * @file DistinctGroupExpansion.cpp
 * Expands distinct groups
 * @since 18/03/2015 Manchester
 * @author Giles
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Connective.hpp"

#include "Options.hpp"
#include "DistinctGroupExpansion.hpp"

using namespace std;
using namespace Shell;

namespace {

/**
 * Replaces every $distinct atom by its expansion, wherever in the formula it sits.
 * Used for the occurrences phase 1 cannot turn into a distinct group.
 */
class DistinctExpander : public FormulaTransformer {
public:
  DistinctExpander(DistinctGroupExpansion& owner) : _owner(owner) {}
protected:
  Formula* applyLiteral(Formula* f) override
  {
    Literal* lit = f->literal();
    if(!Signature::isDistinctLiteral(lit)){
      return f;
    }
    Formula* expansion = _owner.expandLiteral(lit);
    // the parsers only ever build positive $distinct atoms, but do not rely on it
    return lit->isPositive() ? expansion : new NegatedFormula(expansion);
  }
private:
  DistinctGroupExpansion& _owner;
};

/** true if every argument of @c lit is a constant, i.e. the occurrence could be a group */
bool allArgsAreConstants(Literal* lit)
{
  for(unsigned i = 0; i < lit->arity(); i++){
    TermList arg = *lit->nthArgument(i);
    if(!arg.isTerm() || arg.term()->arity() != 0){
      return false;
    }
  }
  return true;
}

}

/**
 * TODO check problem invalidation
 */
void DistinctGroupExpansion::apply(Problem& prb)
{
  if(apply(prb.units())){
    prb.invalidateProperty();
    prb.reportFormulasAdded();
    prb.reportEqualityAdded(false); // Do we need to do this if adding disequality?
  }

}

bool DistinctGroupExpansion::apply(UnitList*& units)
{
  // must run unconditionally: there can be $distinct markers even with no group yet
  bool eliminated = eliminateDistinctPredicates(units);
  bool added = expandGroups(units);
  return eliminated || added;
}

/**
 * Phase 1: replace the given $distinct atom by the conjunction of the corresponding
 * disequalities. The arguments need not be constants (SMT-LIB's distinct accepts
 * arbitrary terms), but they do all have the same sort, which the parsers enforce.
 */
Formula* DistinctGroupExpansion::expandLiteral(Literal* lit)
{
  ASS_G(lit->arity(),1);

  TermList sort = SortHelper::getArgSort(lit,0);
  Stack<TermList> args(lit->arity());
  for(unsigned i = 0; i < lit->arity(); i++){
    ASS_EQ(SortHelper::getArgSort(lit,i),sort);
    args.push(*lit->nthArgument(i));
  }
  return expandTerms(args,sort);
}

/**
 * Phase 1: walk the top level of @c f, which is the formula of @c premise.
 *
 * A $distinct atom sitting at a positive top level and mentioning only constants is
 * the good old case: it holds unconditionally, so it can become a distinct group and
 * disappear from the formula. Anything else -- negative, nested under a disjunction or
 * an implication, or applied to compound terms -- has to be expanded where it stands.
 *
 * Conjectures need no special care here: the parser has already wrapped them in a
 * negation, so they can never look like a positive top-level occurrence.
 */
Formula* DistinctGroupExpansion::processTopLevel(Formula* f, Unit* premise)
{
  switch(f->connective()){
  case LITERAL: {
    Literal* lit = f->literal();
    if(Signature::isDistinctLiteral(lit) && lit->isPositive() && allArgsAreConstants(lit)){
      unsigned grpIdx = env.signature->createDistinctGroup(premise);
      for(unsigned i = 0; i < lit->arity(); i++){
        env.signature->addToDistinctGroup(lit->nthArgument(i)->term()->functor(),grpIdx);
      }
      return Formula::trueFormula();
    }
    break;
  }
  case AND: {
    Stack<Formula*> conjuncts;
    bool changed = false;
    FormulaList::Iterator it(f->args());
    while(it.hasNext()){
      Formula* arg = it.next();
      Formula* newArg = processTopLevel(arg,premise);
      changed |= (newArg != arg);
      if(newArg->connective() != TRUE){ // drop the conjuncts that became $true
        conjuncts.push(newArg);
      }
    }
    if(!changed){
      return f;
    }
    if(conjuncts.isEmpty()){
      return Formula::trueFormula();
    }
    if(conjuncts.size() == 1){
      return conjuncts[0];
    }
    FormulaList* args = FormulaList::empty();
    while(conjuncts.isNonEmpty()){
      FormulaList::push(conjuncts.pop(),args);
    }
    return new JunctionFormula(AND,args);
  }
  case FORALL: {
    // the arguments of a $distinct are ground, so a universal prefix does not matter
    Formula* inner = processTopLevel(f->qarg(),premise);
    if(inner == f->qarg()){
      return f;
    }
    if(inner->connective() == TRUE){
      return inner;
    }
    return new QuantifiedFormula(FORALL,f->vars(),inner);
  }
  default:
    break;
  }

  DistinctExpander expander(*this);
  return expander.transform(f);
}

bool DistinctGroupExpansion::eliminateDistinctPredicates(UnitList*& units)
{
  bool changed = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()){
    Unit* u = uit.next();
    // $distinct is rejected in cnf/tcf, so it can only sit in a formula unit
    if(u->isClause()){
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    Formula* f = fu->formula();
    Formula* nf = processTopLevel(f,fu);
    if(nf == f){
      continue;
    }
    changed = true;
    if(env.options->showPreprocessing()){
      std::cout << "  $distinct elimination: " << f->toString() << " --> " << nf->toString() << endl;
    }
    if(nf->connective() == TRUE){
      // the whole unit was distinctness we have now recorded in the signature
      uit.del();
    } else {
      uit.replace(new FormulaUnit(nf,
        FormulaClauseTransformation(InferenceRule::DISTINCT_EXPANSION,fu)));
    }
  }

  return changed;
}

/**
 * Phase 2: attempts to expand each recorded distinct group
 * (this includes those for builtin sorts i.e. ints, strings...)
 * If all groups are expanded we indicate there are no distinct groups left, which will
 * prevent the distinct simplifier being added later
 */
bool DistinctGroupExpansion::expandGroups(UnitList*& units)
{
  bool added=false;

  Stack<Signature::DistinctGroupMembers>& group_members = env.signature->distinctGroupMembers();

  bool expandEverything = (_expandUpToSize == 0) ||
     env.options->saturationAlgorithm()==Options::SaturationAlgorithm::FINITE_MODEL_BUILDING;

  bool someLeft = false;

  for(unsigned i=0;i<group_members.size();i++){
    Signature::DistinctGroupMembers members = group_members[i];
    // a group of fewer than two members says nothing, so it neither needs expanding
    // nor counts as left behind: DistinctEqualitySimplifier could not use it anyway
    if(members->size() > 1) {
      if(expandEverything || members->size() <= _expandUpToSize) {
        added=true;
        Formula* expansion = expand(*members);
        if(env.options->showPreprocessing()){
          std::cout << "  expansion adding " << expansion->toString() << endl;
        }
        // a group made from a $distinct knows the unit it came from; the ones collected
        // from string constants during parsing have no single unit to point at
        Unit* premise = env.signature->getDistinctGroupPremise(i);
        UnitList::push(
          premise ?
            new FormulaUnit(expansion,
              NonspecificInference1(InferenceRule::DISTINCTNESS_AXIOM,premise)) :
            new FormulaUnit(expansion,
              NonspecificInference0(UnitInputType::AXIOM,InferenceRule::DISTINCTNESS_AXIOM)),
          units);
      }
      else {
        someLeft=true;
      }
    }
  }

  if(!someLeft){
    env.signature->noDistinctGroupsLeft();
  }

  return added;
}

/**
 * If a distinct group of constants has 2 members then a single disequality is created
 * Otherwise a conjunction of disequalities is created
 */
Formula* DistinctGroupExpansion::expand(Stack<unsigned>& constants)
{
  ASS(constants.size()>=2);

  Stack<TermList> terms(constants.size());
  for(unsigned i=0;i<constants.size();i++){
    terms.push(TermList(Term::createConstant(constants[i])));
    ASS(terms.top().isSafe());
  }
  // the members of a group are all of the same sort: string constants are grouped by
  // sort (Signature::getStringDistinctGroup) and $distinct checks its arguments
  return expandTerms(terms,SortHelper::getResultSort(terms[0].term()));
}

/**
 * The quadratic core of the expansion: everything in @c terms is pairwise different.
 */
Formula* DistinctGroupExpansion::expandTerms(Stack<TermList>& terms, TermList sort)
{
  ASS_GE(terms.size(),2);

  // If there are 2 just create a disequality
  if(terms.size()==2){
    return new AtomicFormula(Literal::createEquality(false,terms[0],terms[1],sort));
  }

  // Otherwise create a formula list of disequalities
  FormulaList* diseqs = 0;

  for(unsigned i=0;i<terms.size();i++){
    for(unsigned j=0;j<i;j++){
      Formula* new_dis = new AtomicFormula(Literal::createEquality(false,terms[i],terms[j],sort));
      if(diseqs) FormulaList::push(new_dis,diseqs);
      else diseqs = new FormulaList(new_dis);
    }
  }

  // and create an AND junction of these
  return new JunctionFormula(Connective::AND, diseqs);

}

