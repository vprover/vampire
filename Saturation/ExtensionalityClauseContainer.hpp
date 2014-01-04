#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

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
  ExtensionalityClauseContainer() {}
  void addIfExtensionality(Clause* c);
  void remove(Clause* c);
  ExtensionalityClauseIterator iterator();
  void print(ostream& o);
private:
  ExtensionalityClauseList* _clauses;
  void add(ExtensionalityClause c);
};

}

#endif /*__ExtensionalityClauseContainer__*/
