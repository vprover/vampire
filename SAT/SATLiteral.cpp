
/*
 * File SATLiteral.cpp.
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
 * @file SATLiteral.cpp
 * Implements class SATLiteral.
 */

#include <ostream>

#include "Shell/Options.hpp"

#include "Lib/Int.hpp"

#include "Kernel/Term.hpp"

#include "SATLiteral.hpp"


namespace SAT
{

using namespace std;
using namespace Lib;
using namespace Shell;

vstring SATLiteral::toString() const
{
  if(isPositive()) {
    return Int::toString(var());
  } else {
    return "~"+Int::toString(var());
  }
}

std::ostream& operator<< (std::ostream& out, const SAT::SATLiteral& lit )
{
  return out<<lit.toString();
}

};

