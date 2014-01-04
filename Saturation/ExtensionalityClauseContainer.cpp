#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

namespace Saturation
{

/**
 * Check if clause has exactly one positive equality between variables.
 * If so, track in extensionality container for additional inferences.
 * 
 * Intended to be called when clause is added to the passive container.
 * Extensionality bit in clause is used to check if clause is already
 * in extensionality container (reactivation) or has to be removed
 * (deletion from search space).
 */
void ExtensionalityClauseContainer::addIfExtensionality(Clause* c) {
  if (c->isExtensionality())
    return;
  
  Literal* varEq = 0;
  
  for (Clause::Iterator ci(*c); ci.hasNext(); ) {
    Literal* l = ci.next();

    if (l->isTwoVarEquality() && l->isPositive()) {
      if (varEq != 0)
	return;

      varEq = l;
    }
  }

  if (varEq != 0) {
    c->setExtensionality(true);
    add(ExtensionalityClause(c, varEq, SortHelper::getEqualityArgumentSort(varEq)));
  }
}

void ExtensionalityClauseContainer::add(ExtensionalityClause c) {
  ExtensionalityClauseList::push(c, _clauses);
}

/**
 * Remove clause from extensionality container.
 */
void ExtensionalityClauseContainer::remove(Clause* c) {
  ExtensionalityClauseList::DelIterator it(_clauses);
  while(it.hasNext()) {
    if (it.next().clause == c) {
      it.del();
      break;
    }
  }
}

ExtensionalityClauseIterator ExtensionalityClauseContainer::iterator() {
  return pvi(ExtensionalityClauseList::Iterator(_clauses));
}

void ExtensionalityClauseContainer::print (ostream& out) {
  out << "#####################" << endl;
  ExtensionalityClauseList::Iterator it(_clauses);
  
  while(it.hasNext()) {
    ExtensionalityClause c = it.next();
    out	<< c.clause->toString() << endl
	<< c.literal->toString() << endl
	<< c.sort << endl;
  }

  out << "#####################" << endl;
}

}
