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
 * @file SymElOutput.cpp
 * Implements class SymElOutput.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SaturationAlgorithm.hpp"

#include "SymElOutput.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

SymElOutput::SymElOutput()
{
  env.beginOutput();
  for(unsigned i = 0; i < env.signature->functions(); i++)
    _printer.printTypeDecl(env.signature->getFunction(i), env.out());
  for(unsigned i = 1; i < env.signature->predicates(); i++)
    _printer.printTypeDecl(env.signature->getPredicate(i), env.out());
  env.endOutput();
}

void SymElOutput::init(SaturationAlgorithm* sa)
{
  CALL("SymElOutput::init");

  _sa=sa;
}

void SymElOutput::onAllProcessed()
{
  CALL("SymElOutput::onAllProcessed");

  _eliminated.reset();
}

void SymElOutput::onNonRedundantClause(Clause* c)
{
  CALL("SymElOutput::onNonRedundantClause");

  if(c->color() == COLOR_TRANSPARENT && !c->skip() && _eliminated.contains(c))
    outputSymbolElimination(c);
}

void SymElOutput::onParenthood(Clause* cl, Clause* parent)
{
  CALL("SymElOutput::onParenthood");
  // when a colour is eliminated from a clause
  if(parent->color() != COLOR_TRANSPARENT && cl->color() == COLOR_TRANSPARENT) {
    _eliminated.insert(cl);
  }
  // when a previously-eliminated clause is simplified
  else if(parent->color() == COLOR_TRANSPARENT && _eliminated.contains(parent)) {
    _eliminated.remove(parent);
    _eliminated.insert(cl);
  }
}

void SymElOutput::outputSymbolElimination(Clause* c)
{
  CALL("SymElOutput::outputSymbolElimination");
  ASS_EQ(c->color(),COLOR_TRANSPARENT);
  ASS(!c->skip());

  // don't print eliminated clauses twice: can happen with e.g. AVATAR
  vostringstream sstr;
  _printer.printAsAssertion(c, sstr, _sa->getSplitter());
  if(_alreadyPrinted.insert(sstr.str())) {
    env.beginOutput();
    env.out() << sstr.str();
    env.endOutput();
  }
}

}