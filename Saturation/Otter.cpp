
/*
 * File Otter.cpp.
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
 * @file Otter.cpp
 * Implements class Otter.
 */

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPPrinter.hpp"

#include "Otter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Otter::Otter(Problem& prb, const Options& opt)
  : SaturationAlgorithm(prb, opt)
{
}

ClauseContainer* Otter::getSimplifyingClauseContainer()
{
  return &_simplCont;
}

void Otter::onActiveRemoved(Clause* cl)
{
  CALL("Otter::onActiveRemoved");

  if(cl->store()==Clause::ACTIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onActiveRemoved(cl);
}

void Otter::onPassiveAdded(Clause* cl)
{
  CALL("Otter::onPassiveAdded");

  SaturationAlgorithm::onPassiveAdded(cl);

  if(cl->store()==Clause::PASSIVE) {
    _simplCont.add(cl);

    static Options::WatchNewPassiveClauses watch_option = env.options->watchNewPassiveClauses();

    if (watch_option != Options::WatchNewPassiveClauses::OFF) {
      static auto anyvar_prop = [](Literal* lit){ return lit->isEquality() && lit->isNegative() && lit->hasInterpretedConstants(); };
      static auto onevar_prop = [](Literal* lit){ return anyvar_prop(lit) && (lit->vars() >= 1); };
      static auto twovar_prop = [](Literal* lit){ return anyvar_prop(lit) && (lit->vars() >= 2); };

      static auto has_prop =
        watch_option == Options::WatchNewPassiveClauses::ANYVAR? anyvar_prop :
        ( watch_option == Options::WatchNewPassiveClauses::ONEVAR? onevar_prop:twovar_prop) ;

      //dumping interesting clauses
      bool have_out = env.haveOutput();
      if (!have_out) {
        env.beginOutput();
      }
      Clause::Iterator cl_it(*cl);
      while(cl_it.hasNext()) {
        auto lit = cl_it.next();
        if ( has_prop(lit) ) {
          //select if literal is a negative equality with at least two variables and theory symbols
          Formula* f = Kernel::Formula::fromClause(cl);
          FormulaUnit* fu = new FormulaUnit(f,cl->inference(),cl->inputType() == Unit::CONJECTURE ? Unit::NEGATED_CONJECTURE : cl->inputType()); // CONJECTURE is evil, as it cannot occur multiple times
          env.out() << TPTPPrinter::toString(fu);
        }
        break;
      }

      if (!have_out) {
        env.endOutput();
      }
    }
  }
}

void Otter::onPassiveRemoved(Clause* cl)
{
  CALL("Otter::onPassiveRemoved");

  if(cl->store()==Clause::PASSIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  CALL("Otter::onClauseRetained");

  SaturationAlgorithm::onClauseRetained(cl);

  backwardSimplify(cl);
}

void Otter::onSOSClauseAdded(Clause* cl)
{
  CALL("Otter::onSOSClauseAdded");
  ASS(cl);
  ASS_EQ(cl->store(), Clause::ACTIVE);

  SaturationAlgorithm::onSOSClauseAdded(cl);

  _simplCont.add(cl);
}

void Otter::handleUnsuccessfulActivation(Clause* c)
{
  CALL("Otter::handleUnsuccessfulActivation");

  ASS_EQ(c->store(), Clause::SELECTED);
  _simplCont.remove(c);
  c->setStore(Clause::NONE);
}

}
