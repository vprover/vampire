/**
 * @file Tautology.hpp
 * Defines class Tautology implementing tautology-checking.
 * @since 05/01/2008 Torrevieja
 */

#ifndef __Tautology__
#define __Tautology__

namespace Kernel {
  class Clause;
  class Literal;
}

using namespace Kernel;

namespace Resolution {

/**
 * Class Tautology implementing tautology-checking.
 * @since 05/01/2008 Torrevieja
 */
class Tautology
{
public:
  static bool isTautology(Clause* c);
private:
  static int compare(Literal* l1,Literal* l2);
  static void sort(Literal** l,int to);
}; // class Tautology

}

#endif
