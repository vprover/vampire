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
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#if VHOL

#include "Kernel/HOLMatching.hpp"
#include "Kernel/ApplicativeHelper.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

bool HOLInstantiation::associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub)
{
  CALL("HOLInstantiation::associate");

  TermList query(specialVar, /* special */ true);
  return match(query, node, sub, VarBank::QUERY_BANK);  
}

bool HOLGeneralisation::associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub)
{
  CALL("HOLGeneralisation::associate");

  TermList query(specialVar, /* special */ true);
  return HOLInstantiation::match(node, query, sub, VarBank::NORM_RESULT_BANK);  
}

}

}

#endif