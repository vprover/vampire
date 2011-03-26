/**
 * @file Grounder.hpp
 * Defines class Grounder.
 */

#ifndef __Grounder__
#define __Grounder__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

namespace InstGen {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class Grounder {
public:
  Grounder();

  SATClause* ground(Clause* cl);
  SATLiteral ground(Literal* lit);

  unsigned satVarCnt() const { return _nextSatVar; }

private:
  class CollapsingApplicator;
  Literal* collapseVars(Literal* lit);

  unsigned _nextSatVar;
  DHMap<Literal*, unsigned> _asgn;
};

}

#endif // __Grounder__
