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
 * @file FOOLParamodulation.cpp
 * Implements the inference rule, that is needed for efficient treatment of
 * boolean terms. The details of why it is needed are in the paper
 * "A First Class Boolean Sort in First-Order Theorem Proving and TPTP"
 * by Kotelnikov, Kovacs and Voronkov [1].
 *
 * [1] http://arxiv.org/abs/1505.01682
 */

#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/RapidHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Skolem.hpp"

#include "ChainReasoning.hpp"

namespace Inferences {

void ChainReasoning::attach(SaturationAlgorithm* salg)
{
  CALL("ChainReasoning::attach");

  GeneratingInferenceEngine::attach(salg);
  _chainIndex=static_cast<ChainReasoningChainTermIndex*> (
    _salg->getIndexManager()->request(CHAIN_TERM_INDEX) );
  _boundIndex=static_cast<ChainReasoningLengthClauseIndex*> (
    _salg->getIndexManager()->request(CHAIN_BOUND_INDEX) );
}

void ChainReasoning::detach()
{
  CALL("ChainReasoning::detach");

  _chainIndex=0;
  _boundIndex=0;
  _salg->getIndexManager()->release(CHAIN_TERM_INDEX);
  _salg->getIndexManager()->release(CHAIN_BOUND_INDEX);
  GeneratingInferenceEngine::detach();
}



ClauseIterator ChainReasoning::generateClauses(Clause* premise)
{
  CALL("ChainReasoning::generateClauses");

  using number = NumTraits<IntegerConstantType>;
  static auto one  = TermList(number::oneT());

  ClauseStack resultStack;

  auto createChainOneShorter = [](TermList chainTerm){
    Term* ct = chainTerm.term();

    TermList structSort = SortHelper::getResultSort(ct);

    auto strct = env.signature->getStructOfSort(structSort);
    auto field = strct->getFieldByChain(ct->functor());

    auto location = *ct->nthArgument(0);
    auto time = *ct->nthArgument(1);
    auto length = *ct->nthArgument(2);    
  
    auto nextLoc = TermList(Term::create2(field->functor(), time, location));

    auto lenLessOne = number::add(length, number::minus(one));
  //  auto chainShort = TermList(Term::create(ct->functor(),{location, time, lenLessOne}));

    return TermList(Term::create(ct->functor(),{nextLoc, time, lenLessOne}));
  //  return TermList(Term::create2(field->functor(), time, chainShort));
  };

  TermList num;
  if(premise->length() ==1 && 
     RapidHelper::isZeroLessThanLit((*premise)[0], num)){

    // false means we don't need substitution
    auto results = _chainIndex->getInstances(num, false);
    while(results.hasNext()){
      auto res = results.next();
      TermList len = res.term;
      Literal* lit = res.literal;
      Clause* c = res.clause;
      TermList chainTerm;
     
      auto rsti = NonVariableNonTypeIterator(lit);
      while (rsti.hasNext()) {
        chainTerm = rsti.next();
        auto func = chainTerm.term()->functor();
        if(env.signature->getFunction(func)->chain()){
          auto length = *chainTerm.term()->nthArgument(2);
          if(length == len){
            break;
          }
        }
      }
     
      auto newLit = EqHelper::replace(lit, chainTerm, createChainOneShorter(chainTerm));

      auto clen = c->length();
      Clause* r = new(clen) Clause(clen, GeneratingInference2(InferenceRule::CHAIN_REASONING, premise, c));
      (*r)[0] = newLit;
      unsigned index = 1;
      for(unsigned i = 0; i < clen; i++){
        if((*c)[i] != lit){
          (*r)[index] = (*c)[i];
          index++;          
        }
      }
      resultStack.push(r);
    }
  }

  if(premise->length() == 1 && env.options->chainUnrolling()){
    Literal* lit = (*premise)[0];

    TermList chainTerm;
    bool chainTermFound = false;

    TermIterator rsti = EqHelper::getSubtermIterator(lit,_salg->getOrdering());
    while (rsti.hasNext()) {
      auto term = rsti.next();
      auto func = term.term()->functor();
      if(env.signature->getFunction(func)->chain()){
        auto length = *term.term()->nthArgument(2);
        auto fun    = env.signature->getFunction(length.term()->functor());
        if(length.isTerm() && (fun->skolem() || fun->finalLoopCount())){
          chainTerm = term;
          chainTermFound = true;
          break;
        }
      }
    }
    
    if(chainTermFound){
      TermList loc = *chainTerm.term()->nthArgument(0);
      TermList tp =  *chainTerm.term()->nthArgument(1);
      TermList len = *chainTerm.term()->nthArgument(2); 

      TermStack args;
      args.push(loc);
      args.push(tp);
      args.push(TermList(number::zeroT()));

      TermList newChainTerm = TermList(Term::create(chainTerm.term()->functor(), 3, args.begin()));

      Literal* l1 = EqHelper::replace(lit, chainTerm, newChainTerm);
      Literal* l2 = number::less(true, TermList(number::zeroT()), len); 

      Clause* r = new(2) Clause(2, GeneratingInference1(InferenceRule::CHAIN_REASONING, premise));
      (*r)[0] = l1;
      (*r)[1] = l2;
      resultStack.push(r);
    }

  }

  LiteralStack lits;
  Clause* sidePrem;
  bool modified = false;
  for(unsigned i = 0; i < premise->length(); i++){
    Literal* lit = (*premise)[i];
    Literal* newLit = lit;
    TermIterator rsti = EqHelper::getSubtermIterator(lit,_salg->getOrdering());
    while (rsti.hasNext()) {
      auto term = rsti.next();
      auto func = term.term()->functor();
      if(env.signature->getFunction(func)->chain()){
        auto length = *term.term()->nthArgument(2);
        if(!length.isVar()){
          auto results = _boundIndex->getGeneralizations(length, false);
          if(results.hasNext()){ 
            modified = true;
            sidePrem = results.next().clause;
            newLit = EqHelper::replace(newLit, term, createChainOneShorter(term));
          }
        }
      }
    }
    lits.push(newLit);
  }
  if(modified){
    resultStack.push(Clause::fromStack(lits, GeneratingInference2(InferenceRule::CHAIN_REASONING, premise, sidePrem)));
  }

  Term* chainTerm;
  Term* valueTerm;
  if(RapidHelper::isChainEqualsValueAt(premise, chainTerm, valueTerm)){
    TermList loc = *chainTerm->nthArgument(0);
    TermList tp =  *chainTerm->nthArgument(1);
    TermList len = *chainTerm->nthArgument(2);
    TermList freshVar = TermList(premise->maxVar() + 1, false);
    TermList value = TermList(valueTerm);

    auto structSort = SortHelper::getResultSort(chainTerm);

    auto strct = env.signature->getStructOfSort(structSort);
    auto field = strct->getFieldByChain(chainTerm->functor());

    auto nullLoc = TermList(Term::createConstant(strct->nullFunctor()));
    auto selVal = TermList(Term::create2(field->functor(), tp, value));

    Literal* l1 = Literal::createEquality(false, selVal, nullLoc, structSort);
    Literal* l2 = Literal::create(field->support(), false, {value, tp, loc, freshVar});
    Literal* l3 = number::less(true, freshVar, TermList(number::zeroT()));
    Literal* l4 = number::less(true, len, freshVar);

    Clause* r = new(4) Clause(4, GeneratingInference1(InferenceRule::CHAIN_REASONING, premise));
    (*r)[0] = l1;
    (*r)[1] = l2;
    (*r)[2] = l3;
    (*r)[3] = l4;   

    resultStack.push(r);
  }


  // if we have two clauses of the form:
  // C1 = chain(loc, tp, len1) = null
  // C2 = chain(loc, tp, len2) = null
  // conclude len1 = len2
  // Potential variants:
  //   1) instead of demanding syntactic equality of location and timepoint
  //      allow them to be unifiable
  //   2) don't insist on unit clauses
  // Implementation could be improved by indexing loc and tp terms in some 
  // way. However, I doubt that this will be a big time gain
  /*if(RapidHelper::isChainEqualsNullClause(premise, chainTerm)){
    if(!_chainTerms.find(chainTerm)){
      DHSet<Term*>::Iterator it(_chainTerms);
      TermList loc = *chainTerm->nthArgument(0);
      TermList tp = *chainTerm->nthArgument(1);

      while(it.hasNext()){
        Term* chainOther = it.next();
        TermList locOther = *chainOther->nthArgument(0);
        TermList tpOther = *chainOther->nthArgument(1);
        if(loc == locOther && tp == tpOther){
          TermList len = *chainTerm->nthArgument(2);
          TermList lenOther = *chainOther->nthArgument(2);
          Literal* eq = Literal::createEquality(true, len, lenOther, AtomicSort::intSort());
          Clause* other = _chainClauses.get(chainOther);  
          Clause* res = new(1) Clause(1, GeneratingInference2(InferenceRule::CHAIN_REASONING, premise, other));
          (*res)[0] = eq;
          resultStack.push(res);
        }
      } 
      _chainTerms.insert(chainTerm);
      ALWAYS(_chainClauses.insert(chainTerm,premise));     
    }

  }*/

  if(!resultStack.size())
    return ClauseIterator::getEmpty();

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(resultStack)));
}

}
