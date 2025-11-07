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
 * @file InnerRewriting.cpp
 * Implements class InnerRewriting.
 */

#include "InnerRewriting.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

bool InnerRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  // look for the first equality which rewrites something and rewrite everything with it (check for EqTaut as you go)
  unsigned len = cl->length();
  for (unsigned i = 0; i < len; i++) {
    Literal* rwLit=(*cl)[i];
    TermList lhs, rhs;
    if (rwLit->isEquality() && rwLit->isNegative() && EqHelper::hasGreaterEqualitySide(rwLit,ordering,lhs,rhs)) {
      for (unsigned j = 0; j < len; j++) {
        if (i != j) {
          Literal* lit = (*cl)[j];
          Literal* nLit = EqHelper::replace(lit,lhs,rhs);
          if (nLit != lit) {
            if(EqHelper::isEqTautology(nLit)) {
              env.statistics->innerRewritesToEqTaut++;
              return true;
            }

            RStack<Literal*> resLits;

            for (unsigned k = 0; k < len; k++) {
              if (k == i) {
                resLits->push(rwLit);
              } else if (k < j) {
                resLits->push((*cl)[k]);
              } else if (k == j) {
                resLits->push(nLit);
              } else {
                Literal* oLit = (*cl)[k];
                Literal* rLit = EqHelper::replace(oLit,lhs,rhs);
                if(EqHelper::isEqTautology(rLit)) {
                  env.statistics->innerRewritesToEqTaut++;
                  return true;
                }
                resLits->push(rLit);
              }
            }

            replacement = Clause::fromStack(*resLits,SimplifyingInference1(InferenceRule::INNER_REWRITING, cl));
            return true;
          }
        }
      }
    }
  }

  return false;
}


}
