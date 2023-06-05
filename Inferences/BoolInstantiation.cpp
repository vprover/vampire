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
 * @file BoolInstantiation.cpp
 * Implements class BoolInstantiation.
 */

#if VHOL

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "BoolInstantiation.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void BoolInstantiation::attach(SaturationAlgorithm* salg)
{
  CALL("BoolInstantiation::attach");

  GeneratingInferenceEngine::attach(salg);
  _boolInstFormIndex=static_cast<BoolInstFormulaIndex*> (
    _salg->getIndexManager()->request(BOOL_INST_FORMULA_INDEX) ); 
}

void BoolInstantiation::detach()
{
  CALL("BoolInstantiation::detach");

  _boolInstFormIndex = 0;
  cout << "RELEASING" << endl;
  _salg->getIndexManager()->release(BOOL_INST_FORMULA_INDEX); 
  GeneratingInferenceEngine::detach();
}

ClauseIterator BoolInstantiation::generateClauses(Clause* premise)
{
  CALL("BoolInstantiation::generateClauses");

  typedef ApplicativeHelper AH;

  if(!premise->derivedFromGoal())
  { return ClauseIterator::getEmpty(); }

  static ClauseStack resultStack;
  resultStack.reset();

  for (unsigned i=0; i<premise->length(); i++) {
    Literal* lit=(*premise)[i];

    TermStack abstractionTerms;
    TermStack instantiations;
    AH::getAbstractionTerms(lit, abstractionTerms);
    while(!abstractionTerms.isEmpty()){
      TermList inst = abstractionTerms.pop();
      if(!_insertedInstantiations.contains(inst)){
        _insertedInstantiations.insert(inst);
        instantiations.push(inst);
      }       
    }

    if(env.options->booleanInstantiation() == Options::BoolInstantiation::ABS_AND_SUBTERM){
      NonVariableNonTypeIterator it(lit);
      while(it.hasNext()){
        Term* term = it.next();
        TermList sort = SortHelper::getResultSort(term);
        TermList t = TermList(term);
        // t : sigma -> o for some sigma
        if(!t.containsLooseIndex() && sort.isArrowSort() && sort.result().isBoolSort()){
          if(!_insertedInstantiations.contains(t)){
            _insertedInstantiations.insert(t);
            instantiations.push(t);
          }   
        }
      }
    }


    while(!instantiations.isEmpty()){
      TermList inst = instantiations.pop();
      TermList sort = SortHelper::getResultSort(inst.term());
      auto it = _boolInstFormIndex->getUnifications(TypedTermList(sort, AtomicSort::superSort()), true);
      while(it.hasNext()){
        TermQueryResult tqr = it.next();
        TermList form  = tqr.unifier->apply(tqr.term, RESULT_BANK);
        TermList instS = tqr.unifier->apply(inst, QUERY_BANK); 

        Literal* l       = tqr.literal;
        TermList lhs     = *lit->nthArgument(0);
        TermList rhs     = *lit->nthArgument(1);
        TermList boolVal = AH::isBool(lhs) ? lhs : rhs;
        bool positive    = AH::isTrue(boolVal) == lit->polarity();
       
        TermList newLhs = AH::app(form, instS);
        TermList newRhs = positive ? AH::top() : AH::bottom();  

        Literal* newLit = Literal::createEquality(true, newLhs, newRhs, AtomicSort::boolSort());
        Clause*  c      = tqr.clause;
        unsigned clen   = c->length();
        

        Clause* res = new(clen) Clause(clen, GeneratingInference1(InferenceRule::BOOL_INSTANTIATION, c));
        (*res)[0] = newLit;
        unsigned next = 0;
        for(unsigned i=0;i<clen;i++) {
          Literal* curr=(*c)[i];
          if(curr!=l) {
            Literal* currAfter = tqr.unifier->apply(curr, RESULT_BANK);
            (*res)[next++] = currAfter;
          }
        }
        resultStack.push(res);
      }      
    }



  } 
  

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(resultStack)));


}

}

#endif