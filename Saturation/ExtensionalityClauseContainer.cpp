#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

namespace Saturation
{

/**
 * Check if clause has positive equality between variables. If so, track
 * in extensionality container for additional inferences.
 */
void ExtensionalityClauseContainer::addIfExtensionality(Clause* c) {
  for (Clause::Iterator ci(*c); ci.hasNext(); ) {
    Literal* l = ci.next();

    if (l->isTwoVarEquality() && l->isPositive()) {
      cout << c->toString() << endl;
      c->setExtensionality(true);
      add(c);
      break;
    }
  }
}

void ExtensionalityClauseContainer::add(Clause* c) {
  ClauseList::push(c, _clauses);
}

void ExtensionalityClauseContainer::remove(Clause* c) {
  _clauses = _clauses->remove(c);
}

}
