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
#include "Kernel/TermTransformer.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ForwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template <class SubtermIterator>
void ForwardDemodulation<SubtermIterator>::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
#if VHOL
    env.property->higherOrder() ?
      _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE) :     
#endif
	    _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );

  _preorderedOnly=getOptions().forwardDemodulation()==Options::Demodulation::PREORDERED;
  _encompassing = getOptions().demodulationEncompassment();
}

template <class SubtermIterator>
void ForwardDemodulation<SubtermIterator>::detach()
{
  CALL("ForwardDemodulation::detach");
  _index=0;
#if VHOL
  env.property->higherOrder() ?
    _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE) :     
#endif  
    _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

template <class SubtermIterator>
bool ForwardDemodulation<SubtermIterator>::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardDemodulation::perform");
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
    SubtermIterator it(lit);
    while(it.hasNext()) {
      TermList trm = TermList(it.next());
      if(!attempted.insert(trm)) {
        //We have already tried to demodulate the term @b trm and did not
        //succeed (otherwise we would have returned from the function).
        //If we have tried the term @b trm, we must have tried to
        //demodulate also its subterms, so we can skip them too.
        it.right();
        continue;
      }

      bool toplevelCheck=getOptions().demodulationRedundancyCheck() && lit->isEquality() &&           
	         (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

      // encompassing demodulation is always fine into negative literals or into non-units
      if (_encompassing) {
        toplevelCheck &= lit->isPositive() && (cLen == 1);        
      }

      TermQueryResultIterator git=
#if VHOL
      env.property->higherOrder() ?
        _index->getHOLGeneralizations(TypedTermList(trm.term())) :
#endif
        _index->getGeneralizations(TypedTermList(trm.term()), true);

      while(git.hasNext()) {
        TermQueryResult qr=git.next();
        ASS_EQ(qr.clause->length(),1);

        if(!ColorHelper::compatible(cl->color(), qr.clause->color())) {
          continue;
        }

        static RobSubstitutionTS subst; 
        bool resultTermIsVar = qr.term.isVar();
#if VHOL
        // in higher-order case, we use a substitution tree for
        // index which does sort checking internally
        if(!env.property->higherOrder()){
#endif
          // to deal with polymorphic matching
          // Ideally, we would like to extend the substitution 
          // returned by the index to carry out the sort match.
          // However, ForwardDemodulation uses a CodeTree as its
          // indexing mechanism, and it is not clear how to extend
          // the substitution returned by a code tree.

          if(resultTermIsVar){
            TermList querySort = SortHelper::getTermSort(trm, lit);
            TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
            subst.reset(); 
            if(!subst.match(eqSort, 0, querySort, 1)){
              continue;        
            }
          }
#if VHOL
        }
#endif

        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS;
        auto subs = qr.unifier;
        if(!subs->isIdentityOnQueryWhenResultBound()) {
          //When we apply substitution to the rhs, we get a term, that is
          //a variant of the term we'd like to get, as new variables are
          //produced in the substitution application.
          ASS(false); // we don't expect to reach here
          TermList lhsSBadVars = subs->applyToResult(qr.term);
          TermList rhsSBadVars = subs->applyToResult(rhs);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(trm);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(trm,qDenorm.apply(rNorm.apply(lhsSBadVars)));
          rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
        } else {
          rhsS = subs->applyToBoundResult(rhs);
        }
#if VHOL
        if(!env.property->higherOrder()){
#endif        
          if(resultTermIsVar){
            rhsS = subst.apply(rhsS, 0);
          }
#if VHOL
        }
#endif
        
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
        if(!preordered && (_preorderedOnly || ordering.compare(trm,rhsS)!=Ordering::GREATER) ) {
          continue;
        }

        // encompassing demodulation is fine when rewriting the smaller guy
        if (toplevelCheck && _encompassing) { 
          // this will only run at most once; 
          // could have been factored out of the getGeneralizations loop, 
          // but then it would run exactly once there
          Ordering::Result litOrder = ordering.getEqualityArgumentOrder(lit);
          if ((trm==*lit->nthArgument(0) && litOrder == Ordering::LESS) || 
              (trm==*lit->nthArgument(1) && litOrder == Ordering::GREATER)) {
            toplevelCheck = false;
          }
        }

        if(toplevelCheck) {
          TermList other=EqHelper::getOtherEqualitySide(lit, trm);
          Ordering::Result tord=ordering.compare(rhsS, other);
          if(tord!=Ordering::LESS && tord!=Ordering::LESS_EQ) {
            if (_encompassing) {
              // last chance, if the matcher is not a renaming
              if (subs->isRenamingOn(qr.term,true /* we talk of result term */)) {
                continue; // under _encompassing, we know there are no other literals in cl
              }
            } else {
              Literal* eqLitS = subs->applyToBoundResult(qr.literal);
              bool isMax=true;
              for(unsigned li2=0;li2<cLen;li2++) {
                if(li==li2) {
                  continue;
                }
                if(ordering.compare(eqLitS, (*cl)[li2])==Ordering::LESS) {
                  isMax=false;
                  break;
                }
              }
              if(isMax) {
                //RSTAT_CTR_INC("tlCheck prevented");
                //The demodulation is this case which doesn't preserve completeness:
                //s = t     s = t1 \/ C
                //---------------------
                //     t = t1 \/ C
                //where t > t1 and s = t > C
                continue;
              }
            }
          }
        }

        Literal* resLit = SubtermReplacer(trm, rhsS).transform(lit);
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

#if VHOL
template class ForwardDemodulation<DemodulationSubtermIt>;
#endif
template class ForwardDemodulation<NonVariableNonTypeIterator>;

}
