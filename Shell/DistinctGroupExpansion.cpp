/**
 * @file DistinctGroupExpansion.cpp
 * Expands distinct groups
 * @since 18/03/2015 Manchester
 * @author Giles
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/List.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Connective.hpp"

#include "Options.hpp"
#include "DistinctGroupExpansion.hpp"

using namespace Shell;

/**
 * TODO check problem invalidation
 */
void DistinctGroupExpansion::apply(Problem& prb)
{
  CALL("DistinctGroupExpansion::apply(Problem&)");

  if(apply(prb.units())){
    prb.invalidateProperty();
    prb.refortFormulasAdded();
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
  CALL("DistinctGroupExpansion::apply(UnitList*&)");

  bool added=false;

  Stack<Stack<unsigned>*> group_members = env.signature->getDistinctGroupMembers();

  // If you update this make sure you update the check in Kernel::Signature::Symol::addToDistinctGroup
  bool expandEverything = 
    env.options->saturationAlgorithm()==Options::SaturationAlgorithm::FINITE_MODEL_BUILDING ||
    env.options->bfnt();

  bool someLeft = false;

  for(unsigned i=0;i<group_members.size();i++){
    Stack<unsigned>* members = group_members[i];
    if(i==0 && !env.signature->strings()) continue; // If there are no strings do not expand group
    if(members->size() > 0){
      // If the non-empty distinct group represents numbers then we need to keep
      // the distinct processing later as new numbers can be generated from the
      // existing ones
      if(i==Sorts::SRT_INTEGER || i==Sorts::SRT_RATIONAL || i==Sorts::SRT_REAL) someLeft=true;

      // This 5 is a magic number, if it is changed then the corresponding
      // 6 should be changed in Kernel::Signature::Symol::addToDistinctGroup
      if( members->size()>1 && (members->size() < 5 || expandEverything)){
        added=true;
        Formula* expansion = expand(*members);
        if(env.options->showPreprocessing()){
          env.out() << "  expansion adding " << expansion->toString() << endl;
        }
        // Currently we just say that these are from the Input, not $distinct or theory of ints
        UnitList::push(new FormulaUnit(expansion, new Inference(Inference::INPUT),Unit::AXIOM),units);
      }
      else someLeft=true;
    }
  } 

  if(!someLeft){ env.signature->noDistinctGroupsLeft(); }

  return added;
}

/**
 * If a distinct group of constants has 2 members then a single disequality is creatd
 * Otherwise a conjunction of disequalities is created
 */
Formula* DistinctGroupExpansion::expand(Stack<unsigned> constants)
{
  CALL("DistinctGroupExpansion::expand");

  ASS(constants.size()>=2);
  // If there are 2 just create a disequality
  if(constants.size()==2){
    TermList a = TermList(Term::createConstant(constants[0]));
    TermList b = TermList(Term::createConstant(constants[1]));
    unsigned sort = SortHelper::getResultSort(a.term());
    return new AtomicFormula(Literal::createEquality(false,a,b,sort));
  }

  // Otherwise create a formula list of disequalities
  FormulaList* diseqs = 0; 

  for(unsigned i=0;i<constants.size();i++){
    TermList a = TermList(Term::createConstant(constants[i]));
    ASS(a.isSafe());
    unsigned sort = SortHelper::getResultSort(a.term());

    for(unsigned j=0;j<i;j++){
      TermList b = TermList(Term::createConstant(constants[j]));
      ASS(b.isSafe());
      
      Formula* new_dis = new AtomicFormula(Literal::createEquality(false,a,b,sort));
      if(diseqs) FormulaList::push(new_dis,diseqs);
      else diseqs = new FormulaList(new_dis);

    }
  }

  // and create an AND junction of these
  return new JunctionFormula(Connective::AND, diseqs);

}

