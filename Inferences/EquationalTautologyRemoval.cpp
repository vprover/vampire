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
 * @file EquationalTautologyRemoval.cpp
 * Implements class EquationalTautologyRemoval.
 */

#include "EquationalTautologyRemoval.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/Clause.hpp"

namespace Inferences
{

Clause* EquationalTautologyRemoval::simplify(Clause* cl)
{
  CALL("EquationalTautologyRemoval::simplify");

  // first check whether it makes sense to trigger CC:
  // 1) there should be at least one negative equality and
  // 2a) there should also be a positive one or
  // 2b) there should be complementary non-equality literals

  bool has_neg_eq = false;
  bool has_pos_eq = false;
  bool has_complement = false;

  static DHSet<int> preds;
  preds.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* lit = (*cl)[i];

    if (lit->isEquality()) {
      if (lit->isNegative()) {
        has_neg_eq = true;
      } else {
        has_pos_eq = true;
      }
    } else {
      ASS_G(lit->functor(),0);

      int pred = lit->isNegative() ? -lit->functor() : lit->functor();

      if (preds.find(-pred)) {
        has_complement = true;
      }

      preds.insert(pred);
    }
  }

  if (!has_neg_eq || (!has_pos_eq && !has_complement)) {
    return cl;
  }

  _cc.reset();

  // insert complements of literals from cl, that could possibly lead to a conflict
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* lit = (*cl)[i];

    if (!lit->isEquality()) {
      int pred = lit->isNegative() ? -lit->functor() : lit->functor();
      if (!preds.find(-pred)) {
        continue;
      }
    }

    // equality predicate and those who have complements go in
    Literal* oplit = Literal::complementaryLiteral(lit);
    _cc.addLiteral(oplit);
  }

  if (_cc.getStatus(false) == DP::DecisionProcedure::UNSATISFIABLE) {
    // cout << "Deep equational: " << cl->toString() << endl;

    env.statistics->deepEquationalTautologies++;
    return 0;
  } else {
    return cl;
  }
}

}
