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
 * @file HOLUnificationHandler.hpp
 * Defines class HOLUnificationHandler for dovetailing of HOL unifiers.
 */

#ifndef __HOLUnificationHandler__
#define __HOLUnificationHandler__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/HOL/Unifier.hpp"

using namespace Kernel;
using namespace Shell;

namespace Saturation {

class HOLUnificationHandler {
public:
  HOLUnificationHandler(const Options& opt);

  Clause* handleClause(Clause* cl);
  ClauseStack iterate(bool& terminated);

  static bool isHolUnifiable(TermList t);

private:
  std::pair<Literal*,Unit*> introduceDefinition(Literal* lit);

  struct UCDef {
    unsigned fun;
    FormulaUnit* def;
  };
  DHMap<Literal*, UCDef> _litToDefMap;

  Stack<HOL::Unifier> _todo;
  Stack<HOL::Unifier> _solved;

  unsigned _index = 0;

  const unsigned _kNumIter;
};

}

#endif // __HOLUnificationHandler__
