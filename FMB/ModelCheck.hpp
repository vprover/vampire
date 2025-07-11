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
 * @file ModelCheck.hpp
 * Defines checking of finite models
 *
 * @since 6/10/2015 Manchester
 * @author Giles
 */

#ifndef __ModelCheck__
#define __ModelCheck__

#include "FiniteModelMultiSorted.hpp"

namespace FMB {

using namespace Lib;
using namespace Kernel;

using std::cout;
using std::endl;

class ModelCheck {
  static void checkIsDomainLiteral(Literal* l, int& single_var, Set<Term*>& domainConstants);
  static void addDefinition(FiniteModelMultiSorted& model,Literal* lit,bool negated,
                          Set<Term*>& domainConstants,
                          DHMap<Term*,unsigned>& domainConstantNumber);
public:
  static void doCheck(UnitList* units);
};

} // namespace FMB

#endif
