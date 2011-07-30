/**
 * @file BFNT.hpp
 * Defines class BFNT used to implement the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */


#ifndef __BFNT__
#define __BFNT__

#include "Forwards.hpp"

namespace Kernel {
  class Unit;
};

using namespace Kernel;

namespace Shell {

/**
 * Class BFNT for implementing the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */
class BFNT
{
public:
  BFNT();
  void apply(UnitList*& units);
private:
  Clause* apply(Clause* cl);

  /** equality proxy symbol signature number */
  unsigned _proxy;
};

};

#endif /* __BFNT__ */
