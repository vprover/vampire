#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"

#include "Lib/Environment.hpp"

namespace Saturation
{

using namespace Kernel;

/**
 * Structure to represent extensionality-like clauses, i.e. (1) a pointer to a
 * clause, (2) a pointer to its single equality between variables and (3) the
 * sort of the equality arguments.
 */
struct ExtensionalityClause
{
  ExtensionalityClause () {}
  ExtensionalityClause (Clause* clause, Literal* literal, unsigned sort)
    : clause(clause), literal(literal), sort(sort) {}
  Clause* clause;
  Literal* literal;
  unsigned sort;
};

typedef List<ExtensionalityClause> ExtensionalityClauseList;
typedef VirtualIterator<ExtensionalityClause> ExtensionalityClauseIterator;

/**
 * Container for tracking extensionality-like clauses, i.e. clauses with exactly
 * one positive equality between variables.
 */
class ExtensionalityClauseContainer
{
public:
  ExtensionalityClauseContainer() {
    _sortCnt = env.sorts->sorts();
    _clausesBySort.init(_sortCnt, 0);
  }
  void addIfExtensionality(Clause* c);
  void remove(Clause* c);
  ExtensionalityClauseIterator activeIterator(unsigned sort);
  void print(ostream& o);
private:
  unsigned _sortCnt;
  DArray<ExtensionalityClauseList*> _clausesBySort;
  void add(ExtensionalityClause c);

  struct ActiveFilterFn;
};

}

#endif /*__ExtensionalityClauseContainer__*/
