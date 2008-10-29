/**
 * @file BinaryResolution.hpp
 * Defines class BinaryResolution implementing binary resolution
 * @since 05/01/2008 Torrevieja
 */

#ifndef __BinaryResolution__
#define __BinaryResolution__

namespace Kernel {
  class Clause;
  class Literal;
}

using namespace Kernel;

namespace Resolution {

class ProofAttempt;

/**
 * Class BinaryResolution implementing literal selection
 * @since 05/01/2008 Torrevieja
 */
class BinaryResolution
{
public:
  BinaryResolution(Clause& c,ProofAttempt& pa)
    : _clause(c),
      _pa(pa)
  {}
  void apply();
private:
  /** The clause to resolve upon */
  Clause& _clause;
  /** The proof attempt */
  ProofAttempt& _pa;
  void apply(int i,Literal* lit);
}; // class BinaryResolution

}

#endif
