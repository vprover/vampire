/**
 * @file SATLiteral.cpp
 * Implements class SATLiteral.
 */

#include <ostream>

#include "../Lib/Int.hpp"

#include "SATLiteral.hpp"


namespace SAT
{

using namespace std;
using namespace Lib;

string SATLiteral::toString() const
{
  if(isPositive()) {
    return Int::toString(var());
  } else {
    return "~"+Int::toString(var());
  }
}

};

std::ostream& operator<< (std::ostream& out, const SAT::SATLiteral& lit )
{
  return out<<lit.toString();
}

