#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

namespace Saturation
{

/**
 * Check if clause has positive equality between variables. If so, track
 * in extensionality container for additional inferences.
 */
void ExtensionalityClauseContainer::addIfExtensionality(Clause* c) {
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

void ExtensionalityClauseContainer::remove(Clause* c) {
  ExtensionalityClauseList::DelIterator it(_clauses);
  while(it.hasNext()) {
    if (it.next()._clause == c) {
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
    out	<< c._clause->toString() << endl
	<< c._literal->toString() << endl
	<< c._sort << endl;
  }

  out << "#####################" << endl;
}

}
