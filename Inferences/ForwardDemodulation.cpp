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
 * @file ForwardDemodulation.cpp
 * Implements class ForwardDemodulation.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "DemodulationHelper.hpp"

#include "ForwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardDemodulation::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );

  _preorderedOnly = getOptions().forwardDemodulation()==Options::Demodulation::PREORDERED;
  _encompassing = getOptions().demodulationRedundancyCheck()==Options::DemodulationRedundancyCheck::ENCOMPASS;
  _precompiledComparison = getOptions().demodulationPrecompiledComparison();
  _helper = DemodulationHelper(getOptions(), &_salg->getOrdering());
}

void ForwardDemodulation::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

template <bool combinatorySupSupport>
bool ForwardDemodulationImpl<combinatorySupSupport>::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  TIME_TRACE("forward demodulation");

  Ordering& ordering = _salg->getOrdering();

  //Perhaps it might be a good idea to try to
  //replace subterms in some special order, like
  //the heaviest first...

  static DHSet<TermList> attempted;
  attempted.reset();

  unsigned cLen=cl->length();
  for(unsigned li=0;li<cLen;li++) {
    Literal* lit=(*cl)[li];
    if (lit->isAnswerLiteral()) {
      continue;
    }
    typename std::conditional<!combinatorySupSupport,
      NonVariableNonTypeIterator,
      FirstOrderSubtermIt>::type it(lit);
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      if(!attempted.insert(trm)) {
        //We have already tried to demodulate the term @b trm and did not
        //succeed (otherwise we would have returned from the function).
        //If we have tried the term @b trm, we must have tried to
        //demodulate also its subterms, so we can skip them too.
        it.right();
        continue;
      }

      bool redundancyCheck = _helper.redundancyCheckNeededForPremise(cl, lit, trm);

      TermQueryResultIterator git=_index->getGeneralizations(trm, true);
      while(git.hasNext()) {
        TermQueryResult qr=git.next();
        ASS_EQ(qr.clause->length(),1);

        if(!ColorHelper::compatible(cl->color(), qr.clause->color())) {
          continue;
        }

        // to deal with polymorphic matching
        // Ideally, we would like to extend the substitution
        // returned by the index to carry out the sort match.
        // However, ForwardDemodulation uses a CodeTree as its
        // indexing mechanism, and it is not clear how to extend
        // the substitution returned by a code tree.
        static RobSubstitution subst;
        bool resultTermIsVar = qr.term.isVar();
        if(resultTermIsVar){
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if(!subst.match(eqSort, 0, querySort, 1)){
            continue;
          }
        }

        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        Ordering::Result argOrder = ordering.getEqualityArgumentOrder(qr.literal);
        bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
  #if VDEBUG
        if(preordered) {
          if(argOrder==Ordering::LESS) {
            ASS_EQ(rhs, *qr.literal->nthArgument(0));
          }
          else {
            ASS_EQ(rhs, *qr.literal->nthArgument(1));
          }
        }
  #endif

        auto subs = qr.unifier;
        ASS(subs->isIdentityOnQueryWhenResultBound());

        if (_precompiledComparison) {
          if (!preordered && (_preorderedOnly || !ordering.isGreater(qr.literal,qr.term,[&subs](TermList t) {
            return subs->applyToBoundResult(t);
          })) ) {
            continue;
          }
        }

        TermList rhsS = subs->applyToBoundResult(rhs);
        if(resultTermIsVar){
          rhsS = subst.apply(rhsS, 0);
        }

        if (!_precompiledComparison) {
          if (!preordered && (_preorderedOnly || ordering.compare(trm,rhsS)!=Ordering::GREATER) ) {
            continue;
          }
        }

        // encompassing demodulation is fine when rewriting the smaller guy
        if (redundancyCheck && _encompassing) {
          // this will only run at most once;
          // could have been factored out of the getGeneralizations loop,
          // but then it would run exactly once there
          Ordering::Result litOrder = ordering.getEqualityArgumentOrder(lit);
          if ((trm==*lit->nthArgument(0) && litOrder == Ordering::LESS) ||
              (trm==*lit->nthArgument(1) && litOrder == Ordering::GREATER)) {
            redundancyCheck = false;
          }
        }

        if (redundancyCheck && !_helper.isPremiseRedundant(cl, lit, trm, rhsS, qr.term, subs.ptr(), true)) {
          continue;
        }

        Literal* resLit = EqHelper::replace(lit,trm,rhsS);
        if(EqHelper::isEqTautology(resLit)) {
          env.statistics->forwardDemodulationsToEqTaut++;
          premises = pvi( getSingletonIterator(qr.clause));
          return true;
        }

        Clause* res = new(cLen) Clause(cLen,
          SimplifyingInference2(InferenceRule::FORWARD_DEMODULATION, cl, qr.clause));
        (*res)[0]=resLit;

        unsigned next=1;
        for(unsigned i=0;i<cLen;i++) {
          Literal* curr=(*cl)[i];
          if(curr!=lit) {
            (*res)[next++] = curr;
          }
        }
        ASS_EQ(next,cLen);

        env.statistics->forwardDemodulations++;

        premises = pvi( getSingletonIterator(qr.clause));
        replacement = res;
        return true;
      }
    }
  }

  return false;
}

// This is necessary for templates defined in cpp files.
// We are happy to do it for ForwardDemodulationImpl, since it (at the moment) has only two specializations:
template class ForwardDemodulationImpl<false>;
template class ForwardDemodulationImpl<true>;

}
