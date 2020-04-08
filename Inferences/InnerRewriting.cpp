
/*
 * File InnerRewriting.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
  CALL("InnerRewriting::perform");

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

            Inference* inf = new Inference1(Inference::INNER_REWRITING, cl);
            Clause* res = new(len) Clause(len, cl->inputType(), inf);

            for (unsigned k = 0; k < len; k++) {
              if (k == i) {
                (*res)[k] = rwLit;
              } else if (k < j) {
                (*res)[k] = (*cl)[k];
              } else if (k == j) {
                (*res)[k] = nLit;
              } else {
                Literal* oLit = (*cl)[k];
                Literal* rLit = EqHelper::replace(oLit,lhs,rhs);
                if(EqHelper::isEqTautology(rLit)) {
                  env.statistics->innerRewritesToEqTaut++;
                  res->destroy();
                  return true;
                }
                (*res)[k] = rLit;
              }
            }

            res->setAge(cl->age());
            env.statistics->innerRewrites++;

            replacement = res;
            return true;
          }
        }
      }
    }
  }

  return false;
}


}
