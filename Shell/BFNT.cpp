/**
 * @file BFNT.hpp
 * Implements class BFNT used to implement the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"

#include "BFNT.hpp"

using namespace Shell;
using namespace std;
using namespace Lib;
using namespace Kernel;

BFNT::BFNT()
{
  _proxy = env.signature->addFreshPredicate(2,"equalish");
}

/**
 * Apply the BFNT transformation to a collection of clauses. This collection will
 * be updated as the result of the transformation. The equality proxy predicate will
 * saved as _proxy and 
 */
void BFNT::apply(UnitList*& units)
{
  CALL("BFNT::apply(UnitList*&)");

  // create equality proxy symbol

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Clause* cl=static_cast<Clause*>(uit.next());
    ASS(cl->isClause());
    Clause* cl2=apply(cl);
    if(cl!=cl2) {
      uit.replace(cl2);
    }
  }
} // BFNT::apply

Clause* BFNT::apply(Clause* cl)
{
  CALL("BFNT::apply(Clause*)");

  int maxVar = -1; // maximal variable
  VirtualIterator<unsigned> varIt = cl->getVariableIterator();
  while (varIt.hasNext()) {
    int var = varIt.next();
    if (var > maxVar) {
      maxVar = var;
    }
  }
  cout << cl->toString() << " : " << maxVar << "\n";
  bool changed;
  // LiteralStack result;
  return cl;
} // BFNT::apply

