/**
 * @file BDDClausifier.hpp
 * Defines class BDDClausifier.
 */

#ifndef __BDDClausifier__
#define __BDDClausifier__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

namespace Kernel {

using namespace Lib;
using namespace SAT;

class BDDClausifier {
public:
  BDDClausifier(bool subsumptionResolution, bool naming=false);

  void clausify(BDDNode* node, SATClauseStack& acc);

  unsigned getCNFVarCount();
private:
  struct CNFStackRec;

  void clausify(BDDNode* node, SATClauseStack& acc, unsigned givenName);
  void clausifyWithSR(BDDNode* node, SATClauseStack& acc, unsigned givenName);
  void clausifyWithoutSR(BDDNode* node, SATClauseStack& acc, unsigned givenName);

  SATClause* buildClause(unsigned givenName, Stack<CNFStackRec>& stack,
      unsigned resolvedCnt=0, unsigned nodeName=0);

  unsigned getName(BDDNode* node);

  bool shouldName(BDDNode* node);

  unsigned assignName(BDDNode* node, SATClauseStack& acc);
  unsigned getCNFVar(unsigned bddVar);


  void introduceNames(BDDNode* node, SATClauseStack& acc);


  unsigned _nextCNFVar;
  unsigned _maxBDDVar;
  bool _useSR;
  bool _naming;
  DHMap<BDDNode*, unsigned> _names;
  DHMap<unsigned, unsigned> _bdd2cnfVars;
};

}

#endif // __BDDClausifier__
