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
    return l->isFlexRigid() && !l->polarity() && !SortHelper::getEqualityArgumentSort(l).isArrowSort();
  }
};


struct ImitateProject::ResultFn
{
  Clause* createRes(InferenceRule rule)
  {
    CALL("ImitateProject::ResultFn::createRes");
  
    Clause* res = new(_cLen) Clause(_cLen, GeneratingInference1(rule, _cl));

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      Literal* currAfter = SubstHelper::apply(curr, _subst);
      (*res)[i] = currAfter;    
    }
    return res;    
  }

  void addProofExtraString(Clause* c, Literal* lit, TermList headFlex, TermList pb, int pos = -1)
  {
    CALL("ImitateProject::ResultFn::addProofExtraString");

    bool projecting = pos > -1;

    vstring litPosition = Lib::Int::toString(_cl->getLiteralPosition(lit));

    vstring suffix = pos == 1 ? "st" : (pos == 2 ? "nd" : (pos == 3 ? "nd" : "th"));
    vstring projArgString = projecting ? ", projecting the " + Int::toString(pos) + suffix + " argument" : "";

    vstring extra = "at literal " + litPosition + projArgString + ", binding: [" 
     + headFlex.toString() + " -> " + pb.toString() + "]";

    if (!env.proofExtra) {
      env.proofExtra = new DHMap<const Unit*,vstring>();
    }
    env.proofExtra->insert(c,extra);
    
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

    { // imitation
      unsigned fVar = _maxVar;

      TermList pb = AH::createGeneralBinding(fVar,headRigid,argsFlex,sortsFlex,deBruijnIndices);

      _subst.bind(headFlex.var(), pb);
      Clause* res = createRes(InferenceRule::IMITATE);

      if(env.options->proofExtra()==Options::ProofExtra::FULL){
        addProofExtraString(res, lit, headFlex, pb);
      }

      results.push(res);
    }

    // projections
    for(unsigned i = 0; i < argsFlex.size(); i++){
      // try and project each of the arguments of the flex head in turn
      _subst.reset();
      TermList arg = argsFlex[i];
      TermList argSort = sortsFlex[i];
      // sort wrong, cannot project this arg
      if(argSort.finalResult() != sort) continue;
      TermList head = arg.head();
      // argument has a rigid head different to that of rhs. no point projecting
      if(head.isTerm() &&  head.deBruijnIndex().isNone() &&  head != headRigid) continue;

      unsigned fVar = _maxVar;
      TermList pb = AH::createGeneralBinding(fVar,deBruijnIndices[i],argsFlex,sortsFlex,deBruijnIndices);

      _subst.bind(headFlex.var(), pb);
      Clause* res = createRes(InferenceRule::PROJECT);     

      if(env.options->proofExtra()==Options::ProofExtra::FULL){
        addProofExtraString(res, lit, headFlex, pb, (int)(argsFlex.size() - i));
      }

      results.push(res);
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
