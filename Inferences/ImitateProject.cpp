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
 * @file EqualityResolution.cpp
 * Implements class EqualityResolution.
 */

#if VHOL

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#include "ImitateProject.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ImitateProject::CanImitateAndProject
{
  bool operator()(Literal* l)
  { 
    ASS(l->isEquality());
    return l->isFlexRigid() && !SortHelper::getEqualityArgumentSort(l).isArrowSort();
  }
};


struct ImitateProject::ResultFn
{
  void getConstraints(TermStack& lhss, TermStack& rhss, TermStack& sorts, LiteralStack& constraints)
  {
    CALL("ImitateProject::ResultFn::getConstraints");
    ASS(!constraints.size());
    ASS(lhss.size() == rhss.size());

    for(unsigned i = 0; i < lhss.length(); i++){
      TermList lhs = SubstHelper::apply(lhss[i], _subst);
      TermList rhs = SubstHelper::apply(rhss[i], _subst);      
      constraints.push(Literal::createEquality(false, lhs, rhs, sorts[i]));
    }
  }

  Clause* createRes(InferenceRule rule, LiteralStack& constraints, Literal* lit, bool sameHeads)
  {
    CALL("ImitateProject::ResultFn::createRes");
  
    unsigned newLen = sameHeads ? _cLen - 1 + constraints.length() : _cLen;
    Clause* res = new(newLen) Clause(newLen, GeneratingInference1(rule, _cl));

    unsigned next = 0;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit || !sameHeads) {
        Literal* currAfter = SubstHelper::apply(curr, _subst);
        (*res)[next++] = currAfter;
      }
    }
    while(!constraints.isEmpty()){
      (*res)[next++] = constraints.pop();
    }
    cout << "IN " << _cl->toString() << endl;
    cout << "OUT " << res->toString() << endl;
    return res;    
  }

  ResultFn(Clause* cl)
      : _cl(cl), _cLen(cl->length()), _maxVar(cl->maxVar()) {}
  ClauseIterator operator() (Literal* lit)
  {
    CALL("ImitateProject::ResultFn::operator()");

    typedef ApplicativeHelper AH;

    ASS(lit->isEquality());
    ASS(lit->isFlexRigid());

    static ClauseStack results;
    results.reset();
    _subst.reset();

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    TermList flexTerm, rigidTerm;

    if(arg0.head().isVar()){
      flexTerm = arg0;
      rigidTerm = arg1;
    } else {
      flexTerm = arg1;
      rigidTerm = arg0;
    }

    // since term is rigid, cannot be a variable
    TermList sort = SortHelper::getResultSort(rigidTerm.term());
    ASS(!sort.isArrowSort());
    TermList headFlex, headRigid;
    TermStack argsFlex;
    TermStack argsRigid;
    TermStack sortsFlex; //sorts of arguments of flex head
    TermStack sortsRigid;
    // after an imitation, or the projection of an argument with a rigid head, 
    // we create a new set of constrainst literals    
    LiteralStack newConstraints; 

    AH::getHeadAndArgs(flexTerm, headFlex, argsFlex);
    AH::getHeadAndArgs(rigidTerm, headRigid, argsRigid);
    ASS(argsFlex.size()); // Flex side is not a variable

    AH::getArgSorts(flexTerm, sortsFlex);
    AH::getArgSorts(rigidTerm, sortsRigid);  

    TermStack deBruijnIndices;    
    for(int i = 0; i < argsFlex.size(); i++){
      // could get away with only creating these when we certainly need them
      // but the logic becomes a lot more complicated
      deBruijnIndices.push(AH::getDeBruijnIndex(i, sortsFlex[i]));
    }

    TermStack args;
    TermStack args2;

    auto surroundWithLambdas = [](TermList t, TermStack& sorts){
      ASS(t.isTerm());
      for(int i = 0; i < sorts.size(); i++){
        t = AH::createLambdaTerm(sorts[i], SortHelper::getResultSort(t.term()), t);
      }
      return t;
    };

    cout << "CLAUSE " << _cl->toString() << endl;

    { // imitation
      unsigned fVar = _maxVar;

      for(unsigned i = 0; i < argsRigid.size(); i++){
        TermList freshVar(++fVar, false);
        TermList varSort = AtomicSort::arrowSort(sortsFlex, sortsRigid[i]);
        args.push(AH::createAppTerm(varSort, freshVar, deBruijnIndices));
        args2.push(AH::createAppTerm(varSort, freshVar, argsFlex));      
      }
      TermList headRigidSort = SortHelper::getResultSort(headRigid.term());
      //pb stands for partial binding
      TermList pb = AH::createAppTerm(headRigidSort, headRigid, args);
      pb = surroundWithLambdas(pb, sortsFlex); 

      _subst.bind(headFlex.var(), pb);
      getConstraints(args2, argsRigid, sortsRigid, newConstraints);
      results.push(createRes(InferenceRule::IMITATE, newConstraints, lit, true));
    }
  
    // projections
    for(unsigned i = 0; i < argsFlex.size(); i++){
      // try and project each of the arguments of the flex head in turn
      _subst.reset();
      args.reset();
      args2.reset();
      TermList arg = argsFlex[i];
      TermList argSort = sortsFlex[i];
      // sort wrong, cannot project this arg
      if(argSort.finalResult() != sort) continue;
      TermList head;
      AH::getHeadAndArgs(arg, head, args2);
      // argument has a rigid head different to that of rhs. no point projecting
      if(!head.isVar() && head != headRigid) continue;

      unsigned fVar = _maxVar;
      for(unsigned j = 0; j < AH::getArity(argSort); j++){
        TermList freshVar(++fVar, false);
        TermList varSort = AtomicSort::arrowSort(sortsFlex, AH::getNthArg(argSort, j + 1));
        args.push(AH::createAppTerm(varSort, freshVar, deBruijnIndices));
        args2.push(AH::createAppTerm(varSort, freshVar, argsFlex));      
      }
      cout << "ARG " << arg.toString() << endl;
      cout << "ARG SORT " << argSort.toString() << endl;
      cout << "INDEX " << deBruijnIndices[i].toString() << endl;
      cout << "INDEX SORT " << SortHelper::getResultSort(deBruijnIndices[i].term()).toString() << endl;
      TermList pb = AH::createAppTerm(argSort, deBruijnIndices[i], args);
      pb = surroundWithLambdas(pb, sortsFlex); 
      cout << "PB " << pb.toString() << endl;

      _subst.bind(headFlex.var(), pb);
      if(!head.isVar()){
        getConstraints(args2, argsRigid, sortsRigid, newConstraints);
      }
      results.push(createRes(InferenceRule::PROJECT, newConstraints, lit, !head.isVar()));
    }
  

    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));;
  }
private:
  Substitution _subst;
  Clause* _cl;
  unsigned _cLen;
  unsigned _maxVar;
};

ClauseIterator ImitateProject::generateClauses(Clause* premise)
{
  CALL("ImitateProject::generateClauses");

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  // selected literals
  auto it1 = premise->getSelectedLiteralIterator();

  // only selected literals which are flex rigid
  auto it2 = getFilteredIterator(it1,CanImitateAndProject());

  // carry out imitations and projections
  auto it3 = getMapAndFlattenIterator(it2,ResultFn(premise));

  return pvi( it3 );
}

}

#endif
