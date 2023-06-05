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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
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
#include "Kernel/SubstHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "PrimitiveInstantiation.hpp"

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

struct PrimitiveInstantiation::IsInstantiable
{
  bool operator()(Literal* l)
  { 
    return l->isFlexRigid() && SortHelper::getEqualityArgumentSort(l).isBoolSort();
  }
};

struct PrimitiveInstantiation::ResultFn
{
  typedef ApplicativeHelper AH;
  typedef pair<unsigned, unsigned> IndexPair;
  typedef Stack<IndexPair> IndexPairStack;

  ResultFn(Clause* cl): _cl(cl), _freshVar(cl->maxVar() + 1){
    TermList sortVar(_freshVar++, false);

    // rather than constantly recreating this stack
    // and pushing on the terms every time we run a prim inst inference
    // another option is to use RobSubstitution and allow it to 
    // rename terms apart. That way, we don't need to worry about freshness 
    // of variables. The potential downside is that the whole RobSubstitution
    // mechanism is complicated and may add its own overhead. Worth investigating 
    // though
    _heads.push(AH::top());
    _heads.push(AH::bottom());
    auto piSet = env.options->piSet();
    switch(piSet){
      case Options::PISet::ALL_EXCEPT_NOT_EQ:
      case Options::PISet::ALL:
        _heads.push(AH::conj());
        _heads.push(AH::disj());
        _heads.push(AH::neg());
        _heads.push(AH::equality(sortVar));
        _heads.push(AH::pi(sortVar));
        _heads.push(AH::sigma(sortVar));
        break;
      case Options::PISet::PRAGMATIC:      
      case Options::PISet::NOT:
        _heads.push(AH::neg());
        break;
      // Equality and Pi and Sigma introduce polymorphism
      // into monomorphic problem...
      case Options::PISet::NOT_EQ_NOT_EQ:
        _heads.push(AH::neg());
        _heads.push(AH::equality(sortVar));
        break;
      case Options::PISet::AND:
        _heads.push(AH::conj());
        break;      
      case Options::PISet::OR:
        _heads.push(AH::disj());
        break;
      case Options::PISet::EQUALS:
        _heads.push(AH::equality(sortVar));
        break;      
      case Options::PISet::PI_SIGMA:
        _heads.push(AH::pi(sortVar));
        _heads.push(AH::sigma(sortVar));
        break;      
    }
  }
  
  Clause* createRes()
  {
    CALL("PrimitiveInstantiation::ResultFn::createRes");
  
    unsigned cLen = _cl->length(); 
    Clause* res = new(cLen) Clause(cLen, GeneratingInference1(InferenceRule::PRIMITIVE_INSTANTIATION, _cl));

    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*_cl)[i];
      Literal* currAfter = SubstHelper::apply(curr, _subst);
      (*res)[i] = currAfter;
    }
    return res;    
  }

  void getSameSortIndices(TermStack& sorts, IndexPairStack& indices){
    CALL("PrimitiveInstantiation::ResultFn::getSameSortIndices");

    for(unsigned i = 0; i < sorts.size(); i++){
      for(unsigned j = i + 1; j < sorts.size(); j++){
        if(sorts[i] == sorts[j]){
          indices.push(make_pair(i, j));
        }
      }
    }
  }

  ClauseIterator operator() (Literal* lit){
    CALL("PrimitiveInstantiation::ResultFn::operator()");

    auto set = env.options->piSet();
    static bool pragmatic = set == Options::PISet::PRAGMATIC;
    static bool include_not_eq = set == Options::PISet::ALL || 
                                 set == Options::PISet::NOT_EQ_NOT_EQ;

    static ClauseStack results;
    results.reset();

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    // Flex term is of form X a1 ... an
    TermList flexTerm = arg0.head().isVar() ? arg0 : arg1;

    // since term is rigid, cannot be a variable
    TermList headFlex;
    TermStack argsFlex;
    TermStack sortsFlex; //sorts of arguments of flex head 

    AH::getHeadArgsAndArgSorts(flexTerm, headFlex, argsFlex, sortsFlex);
    ASS(argsFlex.size() == sortsFlex.size());

    if(!argsFlex.size()){
      // TODO do we really want to do this?
      return ClauseIterator::getEmpty();
    }

    // if any amongst a1 ... an is of sort $o, project that 
    // argument to the top
    for(unsigned i =0; i < sortsFlex.size() && pragmatic; i++){
      if(sortsFlex[i].isBoolSort()){
        _subst.reset();
        TermList gb = AH::surroundWithLambdas(AH::getDeBruijnIndex(i, sortsFlex[i]), sortsFlex);
        _subst.bind(headFlex.var(), gb);
        results.push(createRes());        
      }
    }

    if(pragmatic){
      IndexPairStack sameSortArgs;
      getSameSortIndices(sortsFlex, sameSortArgs);
      for(unsigned i = 0; i < sameSortArgs.size(); i++){
        _subst.reset();
        IndexPair p = sameSortArgs[i];
  
        TermList dbi = AH::getDeBruijnIndex(p.first, sortsFlex[p.first]);
        TermList dbj = AH::getDeBruijnIndex(p.second, sortsFlex[p.second]);

        // creating term dbi = dbj
        TermList tm = AH::app2(AH::equality(sortsFlex[p.first]), dbi, dbj);
        TermList gb = AH::surroundWithLambdas(tm, sortsFlex);
        _subst.bind(headFlex.var(), gb);
        results.push(createRes());     

        //creating dbi != dbj
        _subst.reset();
        gb = AH::surroundWithLambdas(AH::app(AH::neg(), tm), sortsFlex);
        _subst.bind(headFlex.var(), gb);
        results.push(createRes());

        if(sortsFlex[p.first].isBoolSort()){
          //creating dbi \/ dbj
          _subst.reset();
          gb = AH::surroundWithLambdas(AH::app2(AH::disj(), dbi, dbj), sortsFlex);
          _subst.bind(headFlex.var(), gb);
          results.push(createRes());     

          //creating dbi /\ dbj
          _subst.reset();
          gb = AH::surroundWithLambdas(AH::app2(AH::conj(), dbi, dbj), sortsFlex);
          _subst.bind(headFlex.var(), gb);
          results.push(createRes()); 
        }             
      }
    }
    
    // bind head variable to all general bindings produced using heads in _heads
    for(unsigned i =0; i < _heads.size(); i++){
      _subst.reset();
      TermList fVar(_freshVar,false);
      
      bool surround = (!_heads[i].isEquals() || !include_not_eq);
      TermList gb  = AH::createGeneralBinding(fVar,_heads[i],sortsFlex,surround);
      TermList gb2 = surround ? gb : AH::surroundWithLambdas(gb, sortsFlex);

      _subst.bind(headFlex.var(), gb2);
      results.push(createRes());

      if(!surround){
        // add not equals
        _subst.reset();
        gb = AH::surroundWithLambdas(AH::app(AH::neg(), gb), sortsFlex);

        _subst.bind(headFlex.var(), gb);
        results.push(createRes());        
      }
    }

    env.statistics->primitiveInstantiations++;  
    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
  }
  
private:
  TermStack _heads;
  Clause* _cl;
  unsigned _freshVar;
  Substitution _subst;  
};

ClauseIterator PrimitiveInstantiation::generateClauses(Clause* premise)
{
  CALL("PrimitiveInstantiation::generateClauses");
  
  //is this correct?
  auto it1 = premise->getSelectedLiteralIterator();
  //filter out literals that are not suitable for PI
  auto it2 = getFilteredIterator(it1, IsInstantiable());
  //perform instantiations
  auto it3 = getMapAndFlattenIterator(it2, ResultFn(premise));
  
  return pvi( it3 );
}

}

#endif