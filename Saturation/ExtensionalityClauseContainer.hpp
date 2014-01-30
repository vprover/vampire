#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"

#include "Shell/Options.hpp"

#include "Lib/Environment.hpp"

namespace Saturation
{

using namespace Kernel;
using namespace Shell;

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
  ExtensionalityClauseContainer(const Options& opt)
  : _size(0),
    _maxLen(opt.extensionalityMaxLength()),
    _allowPosEq(opt.extensionalityAllowPosEq())
  {
    _onlyKnown = (opt.extensionalityInference() == Options::EI_KNOWN);
    _sortCnt = env.sorts->sorts();
    _clausesBySort.init(_sortCnt, 0);
  }
  Literal* addIfExtensionality(Clause* c);
  static Literal* getSingleVarEq(Clause* c);
  ExtensionalityClauseIterator activeIterator(unsigned sort);
  unsigned size() const { return _size; }
  void print(ostream& o);
private:
  unsigned _sortCnt;
  DArray<ExtensionalityClauseList*> _clausesBySort;
  void add(ExtensionalityClause c);

  struct ActiveFilterFn;

  unsigned _size;
  
  bool _onlyKnown;
  unsigned _maxLen;
  bool _allowPosEq;
};

}

#endif /*__ExtensionalityClauseContainer__*/
