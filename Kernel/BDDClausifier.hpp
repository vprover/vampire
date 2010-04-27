/**
 * @file BDDClausifier.hpp
 * Defines class BDDClausifier.
 */

#ifndef __BDDClausifier__
#define __BDDClausifier__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

namespace Kernel {

using namespace Lib;
using namespace SAT;

class BDDClausifier {
public:
  BDDClausifier(bool naming=false);

  void clausify(BDDNode* node, SATClauseStack& acc);
  unsigned getCNFVarCount();
private:
  void clausifyWithSR(BDDNode* node, SATClauseStack& acc);
  void clausifyWithoutSR(BDDNode* node, SATClauseStack& acc);

  unsigned name(BDDNode* node, SATClauseStack& acc);
  unsigned getCNFVar(unsigned bddVar);

  //struct used in the toCNF function
  struct CNFStackRec;

  unsigned _nextCNFVar;
  unsigned _maxBDDVar;
  bool _useSR;
  bool _naming;
  DHMap<BDDNode*, unsigned> _names;
  DHMap<unsigned, unsigned> _bdd2cnfVars;
};

}

#endif // __BDDClausifier__
