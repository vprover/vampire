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
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Connective.hpp"

#include "Options.hpp"
#include "DistinctGroupExpansion.hpp"

using namespace std;
using namespace Shell;

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

/**
 * Attempts to expand each recorded distinct group
 * (this includes those for builtin sorts i.e. ints, strings...)
 * If all groups are expanded we indicate there are no distinct groups left, which will
 * prevent the distinct simplifier being added later
 */
bool DistinctGroupExpansion::apply(UnitList*& units)
{
  bool added=false;

  Stack<Signature::DistinctGroupMembers>& group_members = env.signature->distinctGroupMembers();

  bool expandEverything = (_expandUpToSize == 0) ||
     env.options->saturationAlgorithm()==Options::SaturationAlgorithm::FINITE_MODEL_BUILDING;

  bool someLeft = false;

  for(unsigned i=0;i<group_members.size();i++){
    Signature::DistinctGroupMembers members = group_members[i];
    if(members->size() > 0) {
      if( members->size()>1 && (expandEverything || members->size() <= _expandUpToSize)) {
        added=true;
        Formula* expansion = expand(*members);
        if(env.options->showPreprocessing()){
          std::cout << "  expansion adding " << expansion->toString() << endl;
        }
        // Currently we just say that these are from the Input, not $distinct or theory of ints
        UnitList::push(
          new FormulaUnit(expansion,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::DISTINCTNESS_AXIOM)),
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
 * The function creates a (possibly empty) conjunction of disequalities
 * between all pairs of constants in the input stack.
 */
Formula* DistinctGroupExpansion::expand(Stack<unsigned>& constants)
{
  // Otherwise create a formula list of disequalities
  auto diseqs = FormulaList::empty();

  for(unsigned i=0;i<constants.size();i++){
    auto a = Term::createConstant(constants[i]);
    ASS(a->shared());
    TermList sort = SortHelper::getResultSort(a);

    for(unsigned j=0;j<i;j++){
      auto b = Term::createConstant(constants[j]);
      ASS(b->shared());
      ASS_EQ(sort, SortHelper::getResultSort(b));

      FormulaList::push(
        new AtomicFormula(Literal::createEquality(false,TermList(a),TermList(b),sort)),
        diseqs);
    }
  }

  // and create an AND junction of these
  return JunctionFormula::generalJunction(Connective::AND, diseqs);

}

