/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __ExtensionalityClauseContainer__
#define __ExtensionalityClauseContainer__

#include "Forwards.hpp"

#include "Kernel/OperatorType.hpp"

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
  ExtensionalityClause (Clause* clause, Literal* literal, TermList sort)
    : clause(clause), literal(literal), sort(sort) {}
  Clause* clause;
  Literal* literal;
  TermList sort;
};

typedef List<ExtensionalityClause> ExtensionalityClauseList;
typedef VirtualIterator<ExtensionalityClause> ExtensionalityClauseIterator;
typedef DHMap<TermList, ExtensionalityClauseList*> ClausesBySort;
/**
 * Container for tracking extensionality-like clauses, i.e. clauses with exactly
 * one positive equality between variables.
 */
class ExtensionalityClauseContainer
{
public:
  CLASS_NAME(ExtensionalityClauseContainer);
  USE_ALLOCATOR(ExtensionalityClauseContainer);

  ExtensionalityClauseContainer(const Options& opt)
  : _size(0),
    _maxLen(opt.extensionalityMaxLength()),
    _allowPosEq(opt.extensionalityAllowPosEq())
  {
    _onlyKnown = (opt.extensionalityResolution() == Options::ExtensionalityResolution::KNOWN);
    _onlyTagged = (opt.extensionalityResolution() == Options::ExtensionalityResolution::TAGGED);
  }
  Literal* addIfExtensionality(Clause* c);
  static Literal* getSingleVarEq(Clause* c);
  ExtensionalityClauseIterator activeIterator(TermList sort);
  unsigned size() const { return _size; }
  void print(ostream& o);
private:
  ClausesBySort _clausesBySort;
  void add(ExtensionalityClause c);

  struct ActiveFilterFn;

  unsigned _size;
  
  bool _onlyKnown;
  bool _onlyTagged;
  unsigned _maxLen;
  bool _allowPosEq;
};

}

#endif /*__ExtensionalityClauseContainer__*/
