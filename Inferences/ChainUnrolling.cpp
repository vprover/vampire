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
 * @file ChainUnrolling.cpp
 * Implements the inference rule, that is needed for efficient treatment of
 * boolean terms. The details of why it is needed are in the paper
 * "A First Class Boolean Sort in First-Order Theorem Proving and TPTP"
 * by Kotelnikov, Kovacs and Voronkov [1].
 *
 * [1] http://arxiv.org/abs/1505.01682
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RapidHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Statistics.hpp"

#include "ChainUnrolling.hpp"

namespace Inferences {

TermList ChainUnrolling::unroll(TermList term, int len)
{
  CALL("ChainUnrolling::unroll");

  ASS(len >= 0);
  ASS(term.isTerm());

  Term* t = term.term();
  auto tSym = env.signature->getFunction(t->functor());
  auto tSymName = tSym->name();
  //TODO, below is very hacky
  auto name = tSymName.substr(0, tSymName.rfind("_"));
  auto fun = env.signature->getFunctionNumber(name,2);

  TermList tl = *t->nthArgument(0);
  TermList tp = *t->nthArgument(1);

  for(int i = 0; i < len; i++){
    tl = TermList(Term::create2(fun, tp, tl));
  }
  return tl;
}

Clause* ChainUnrolling::simplify(Clause* premise)
{
  CALL("ChainUnrolling::simplify");

  TermList subTerm;
  TermList unrolledSubTerm;
  unsigned pos = 0;
  unsigned cLen = premise->length();

  while (pos < cLen) {
    Literal *literal = (*premise)[pos];
    NonVariableNonTypeIterator nvi(literal);

    while (nvi.hasNext()) {
      subTerm = nvi.next();
      int len = RapidHelper::isConcreteLengthChain(subTerm);
      if(len > -1){
        unrolledSubTerm = unroll(subTerm, len);
        ASS(unrolledSubTerm != subTerm);
        goto substitution;
      }
    }
    pos++;
  }

  return premise;

substitution:

  unsigned clen = premise->length();
  Clause* res = new(clen) Clause(clen, 
    SimplifyingInference1(InferenceRule::CHAIN_UNROLLING, premise));

  for (unsigned i = 0; i < clen; i++) {
    (*res)[i] = i == pos ? EqHelper::replace((*premise)[i], subTerm, unrolledSubTerm) : (*premise)[i];
  }

  cout << "PREM " << premise->toString() << endl;
  cout << "RES " << res->toString() << endl;

  env.statistics->chainUnrolls++;
  return res;
}

}
