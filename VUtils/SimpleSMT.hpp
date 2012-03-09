/**
 * @file SimpleSMT.hpp
 * Defines class SimpleSMT.
 */

#ifndef __SimpleSMT__
#define __SimpleSMT__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "SAT/SATLiteral.hpp"
#include "Lib/Numbering.hpp"


namespace VUtils {

  using namespace Kernel;
  using namespace Shell;
  using namespace SAT;

  typedef DHMap<Literal *, int> MyMap;
  typedef Numbering<Literal *, 1 > TwoWayMap;

  class SimpleSMT {
  public:
    int perform(int argc, char** argv);
  protected:
    // LiteralStack createAssignedLiteralsStack(TwoWayMap& map, Lib::ScopedPtr<SAT::SATSolver> solver);
    SAT::SATLiteral litTOSAT(Literal *l, TwoWayMap& map);
  };
}

#endif // __SimpleSMT__
