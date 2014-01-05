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
  if(c.sort == Sorts::SRT_INTEGER) {
    c.clause->setExtensionality(false);
    return;
  }
  ExtensionalityClauseList::push(c, _clausesBySort[c.sort]);
}

/**
 * Remove clause from extensionality container.
 */
void ExtensionalityClauseContainer::remove(Clause* c) {
  c->setExtensionality(false);
  
  for(size_t i = 0; i < _clausesBySort.size(); ++i) {
    ExtensionalityClauseList::DelIterator it(_clausesBySort[i]);
    while(it.hasNext()) {
      if (it.next().clause == c) {
	it.del();
	break;
      }
    }
  }
}

struct ExtensionalityClauseContainer::ActiveFilterFn
{
  ActiveFilterFn() {}
  DECL_RETURN_TYPE(bool);
  bool operator()(ExtensionalityClause extCl)
  {
    return extCl.clause->store() == Clause::ACTIVE;
  }
};

ExtensionalityClauseIterator ExtensionalityClauseContainer::activeIterator(unsigned sort) {
  return pvi(getFilteredIterator(
	       ExtensionalityClauseList::Iterator(_clausesBySort[sort]),
	       ActiveFilterFn()));
}

void ExtensionalityClauseContainer::print (ostream& out) {
  out << "#####################" << endl;

  for(size_t i = 0; i < _clausesBySort.size(); ++i) {
    ExtensionalityClauseList::Iterator it(_clausesBySort[i]);
    while(it.hasNext()) {
      ExtensionalityClause c = it.next();
      out << c.clause->toString() << endl
	  << c.literal->toString() << endl
	  << c.sort << endl;
    }
  }
  
  out << "#####################" << endl;
}

}
