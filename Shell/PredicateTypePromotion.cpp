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
 * @file PredicateTypePromotion.cpp
 * A preprocessing step which lifts unary predicates to sorts in some cases
 */

#include "PredicateTypePromotion.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"

#include <unordered_set>

using namespace Kernel;

namespace Shell {

void PredicateTypePromotion::apply(Kernel::Problem &prb) {
  UnitList *units = prb.units();
  UnitList::Iterator uit(units);
  std::unordered_set<unsigned> possible;
  for(unsigned i = 0; i < env.signature->predicates(); i++) {
    if(env.signature->getPredicate(i)->arity() == 1)
      possible.insert(i);
  }
  while(uit.hasNext()) {
    Clause *cl = uit.next()->asClause();
    for(Literal *l : cl->iterLits()) {
      unsigned p = l->functor();
      if(!possible.count(p))
        continue;
      if(l->polarity() && cl->length() != 1) {
        possible.erase(p);
        continue;
      }
      TermList arg = l->termArg(0);
      if(arg.isTerm() && arg.term()->arity()) {
        possible.erase(p);
        continue;
      }
    }
  }
  for(unsigned p : possible)
    std::cout << "sort detected: " << env.signature->predicateName(p) << '\n';
}

}
