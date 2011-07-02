/**
 * @file ModelPrinter.hpp
 * Defines class ModelPrinter.
 */

#ifndef __ModelPrinter__
#define __ModelPrinter__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"


namespace InstGen {

using namespace Kernel;
using namespace SAT;

class ModelPrinter {
public:
  ModelPrinter(IGAlgorithm& iga);

  bool tryOutput(ostream& stm);

private:

  struct InstLitComparator;

  static bool isEprProblem();
  static bool isEquality(Literal* lit);

  void collectTrueLits();
  void getInstances(LiteralStack& trueLits, TermStack& domain, LiteralStack& instanceAcc);
  void generateNewInstances(Literal* base, TermStack& domain, DHSet<Literal*>& instSet, LiteralStack& instAcc);
  void analyzeEquality();
  void populateDomain();

  Stack<TermList> _domain;

  /** Maps terms to representants of their equivalence classes */
  DHMap<TermList,TermList> _rewrites;

  LiteralStack _trueLits;
  LiteralStack _trueEqs;

  IGAlgorithm& _iga;
};

}

#endif // __ModelPrinter__
