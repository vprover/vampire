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
 * @file HOLUnifier.hpp
 * Defines class HOLUnifier for dovetailing of HOL unifiers.
 */

#ifndef __HOLUnifier__
#define __HOLUnifier__

#include "Forwards.hpp"
#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"

using namespace Kernel;

namespace Saturation {

class HOLUnifier {
public:
  Clause* handleClause(Clause* cl);

  static bool isHolUnifiable(TermList t);

private:
  Literal* introduceDefinition(Literal* lit);

  Stack<FormulaUnit*> _defs;
  DHMap<Literal*, unsigned> _defPredMap;
};

}

#endif // __HOLUnifier__
