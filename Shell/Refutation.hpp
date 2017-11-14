
/*
 * File Refutation.hpp.
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
 * @file Refutation.hpp
 * Defines the class for printing refutations
 * @since 04/01/2008 Torrevieja
 */

#ifndef __Refutation__
#define __Refutation__

#include <ostream>

#include "Forwards.hpp"

namespace Shell {

using namespace std;
using namespace Kernel;

/**
 * Class implementing refutations
 * @since 04/01/2008 Torrevieja
 */
class Refutation
{
public:
  Refutation(Unit* unit,bool detailed);
  void output(ostream&);

  /** equality function, required for hashing units */
  inline static bool equals(const Unit* u1,const Unit* u2)
  { return (void*)u1 == (void*)u2; }
  static unsigned hash(Unit*);
private:
  /** The last unit of the refutation  */
  Unit* _goal;
  /** True if the output should also include include formula inferences */
  // bool _detailed; // MS: unused
}; // class Refutation

}

#endif
