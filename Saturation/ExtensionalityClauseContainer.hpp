#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

namespace Saturation
{

using namespace Kernel;

struct ExtensionalityClause
{
  ExtensionalityClause () {}
  ExtensionalityClause (Clause* clause, Literal* literal, unsigned sort)
    : _clause(clause), _literal(literal), _sort(sort) {}
  Clause* _clause;
  Literal* _literal;
  unsigned _sort;
};

typedef List<ExtensionalityClause> ExtensionalityClauseList;
typedef VirtualIterator<ExtensionalityClause> ExtensionalityClauseIterator;

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
