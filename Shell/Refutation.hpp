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
  
  static Comparison compare(Unit* u1,Unit* u2);
private:
  /** The last unit of the refutation  */
  Unit* _goal;
  /** True if the output should also include include formula inferences */
  bool _detailed;
}; // class Refutation

}

#endif
