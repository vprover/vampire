/**
 * @file TPTP.hpp
 * Defines class TPTP for printing various objects in the TPTP syntax.
 *
 * @since 12/04/2008 Manchester
 */

#ifndef __TPTP__
#define __TPTP__

#include <iostream>

#include "Forwards.hpp"

namespace Shell {

using namespace std;
using namespace Kernel;

/**
 * Class TPTP
 * @since 12/04/2008 Manchester
 */
class TPTP 
{
public:
  static string toString(const Unit*);
  static string toString(const Formula*);
  static string toString(const Term*);
  static string toString(const Literal*);
}; // class TPTP

}

#endif

