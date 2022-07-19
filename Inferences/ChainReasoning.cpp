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

    auto location = *ct->nthArgument(0);
    auto time = *ct->nthArgument(1);
    auto length = *ct->nthArgument(2);    
    
    auto chainName = env.signature->getFunction(ct->functor())->name();                     

    // TODO, this is bad, we should not be manipulating strings like this
    auto pos = chainName.find_last_of("_");
    auto nextName = chainName.substr(0, pos);

    auto next = env.signature->getFunctionNumber(nextName, 2);
    auto nextLoc = TermList(Term::create2(next, time, location));

    auto lenLessOne = number::add(length, number::minus(one));
    return TermList(Term::create(ct->functor(),{nextLoc, time, lenLessOne}));
  };

  if(premise->length() ==1 && 
     RapidHelper::isZeroLessThanLit((*premise)[0])){
    auto lit = (*premise)[0];
    TermList arg2 = *lit->nthArgument(1);

    // false means we don't need substitution
    auto results = _chainIndex->getInstances(arg2, false);
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

    auto chainTermSort = SortHelper::getResultSort(chainTerm);
    auto sName = chainTermSort.term()->toString();
    auto cName = env.signature->getFunction(chainTerm->functor())->name();

    //std::transform(sName.begin(), sName.begin() + 1, sName.begin(), ::tolower);
    // hard coding for now to avoid having to sanitise 'Node()'
    auto nullName = "node_null_loc";
    auto selName = "node_next";

    auto nullLoc = env.signature->getFunctionNumber(nullName, 0);
    auto sel     = env.signature->getFunctionNumber(selName, 2);    
    auto nullLocT = TermList(Term::createConstant(nullLoc));
    auto selValT = TermList(Term::create2(sel, tp, value));

    auto supName = "in_support_" + cName;
    auto supPred = env.signature->getPredicateNumber(supName, 4);

    Literal* l1 = Literal::createEquality(false, selValT, nullLocT, chainTermSort);
    Literal* l2 = Literal::create(supPred, false, {value, tp, loc, freshVar});
    Literal* l3 = number::less(true, freshVar, TermList(number::zeroT()));
    Literal* l4 = number::less(true, len, freshVar);

    Clause* r = new(4) Clause(4, GeneratingInference1(InferenceRule::CHAIN_REASONING, premise));
    (*r)[0] = l1;
    (*r)[1] = l2;
    (*r)[2] = l3;
    (*r)[3] = l4;   

    cout << "R IS " << r->toString() << endl;
    resultStack.push(r);
  }

  if(RapidHelper::isChainEqualsNullClause(premise, chainTerm)){
    auto sort = AtomicSort::intSort();
    auto chainTermSort = SortHelper::getResultSort(chainTerm);

    unsigned freshVar = premise->maxVar() + 1;
    TermList x = TermList(freshVar, false);
    TermList y = TermList(freshVar + 1, false);
    
    TermList arg0 = *chainTerm->nthArgument(0);
    TermList arg1 = *chainTerm->nthArgument(1);
    TermList xLenChain = TermList(Term::create(chainTerm->functor(), {arg0, arg1, x}));
    TermList yLenChain = TermList(Term::create(chainTerm->functor(), {arg0, arg1, y}));

    Literal* varEq = Literal::createEquality(true, x, y, sort);
    Literal* disequality = Literal::createEquality(false, xLenChain, yLenChain, chainTermSort);

    Clause* res = new(2) Clause(2, GeneratingInference1(InferenceRule::CHAIN_REASONING, premise));
    (*res)[0] = varEq;
    (*res)[1] = disequality;
    resultStack.push(res);
  }

  if(!resultStack.size())
    return ClauseIterator::getEmpty();

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(resultStack)));
}

}
