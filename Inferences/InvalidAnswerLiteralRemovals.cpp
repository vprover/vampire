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
 * @file InvalidAnswerLiteralRemoval.cpp
 * Implements class UncomputableAnswerLiteralRemoval.
 */

#include "Kernel/Clause.hpp"
#include "Parse/TPTP.hpp"

#include "InvalidAnswerLiteralRemovals.hpp"

namespace Inferences
{

Clause* UncomputableAnswerLiteralRemoval::simplify(Clause* cl)
{
  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral() && !lit->computableOrVar())
      return nullptr;
  }
  return cl;
}

UndesiredAnswerLiteralRemoval::UndesiredAnswerLiteralRemoval(const vstring& avoidThese)
{
  // TODO: catch parsing exceptions and complain properly
  _avoiders = Parse::TPTP::parseClauseFromString(avoidThese);
  // std::cout << "Got: " << _avoiders->toString() << std::endl;
}

Clause* UndesiredAnswerLiteralRemoval::simplify(Clause* cl)
{
  static RobSubstitution helperSubst;

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral() && lit->isNegative()) {
      for (Literal* toAvoid : _avoiders->iterLits()) {
        if (lit->functor() == toAvoid->functor()) {
          helperSubst.reset();
          if (helperSubst.matchArgs(toAvoid,0,lit,1)) {
            return nullptr;
          }
        }
      }
    }
  }

  return cl;
}

}
