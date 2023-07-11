/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/NumTraits.hpp"

#include "Shell/Statistics.hpp"

#include "ChainSimp.hpp"

namespace Inferences {

Clause* ChainSimp::simplify(Clause* premise) {
  CALL("ChainSimp::simplify");

  using number = NumTraits<IntegerConstantType>;

  TermList subTerm;
  TermList simpedSubTerm;
  unsigned literalPosition = 0;
  unsigned cLen = premise->length();

  while (literalPosition < cLen) {
    Literal *literal = (*premise)[literalPosition];
    NonVariableNonTypeIterator nvi(literal);

    while (nvi.hasNext()) {
      subTerm = nvi.next();
      auto func = subTerm.term()->functor();
      if(env.signature->getFunction(func)->chain()){
        auto length = *subTerm.term()->nthArgument(2);
        if(number::isZero(length)){
          simpedSubTerm = *subTerm.term()->nthArgument(0);
          goto simlify_stage;
        }
      }
    }
    literalPosition++;
  }

  return premise;

simlify_stage:

  unsigned conclusionLength = premise->length();
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength, SimplifyingInference1(InferenceRule::CHAIN_REASONING, premise));

  for (unsigned i = 0; i < conclusion->length(); i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], subTerm, simpedSubTerm) : (*premise)[i];
  }

  return conclusion;
}



}
