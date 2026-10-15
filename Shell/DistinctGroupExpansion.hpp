/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file DistinctGroupExpansion.hpp
 * Defines expansion of distinct groups
 */

#ifndef __DistinctGroupExpansion__
#define __DistinctGroupExpansion__

#include "Forwards.hpp"

namespace Shell{

using namespace Kernel;

/**
 * Gets rid of all knowledge about distinctness that is still only recorded
 * symbolically, in two phases:
 *
 * 1) every $distinct marker literal left behind by the parsers (see
 *    Signature::getDistinctPredicate) is eliminated. An occurrence at a positive
 *    top level mentioning only constants becomes a distinct group -- the parser
 *    could not do this itself, as it does not know where in the formula it is --
 *    and any other occurrence is expanded into disequalities on the spot;
 *
 * 2) the distinct groups (those just created, plus the ones the string constants
 *    were collected into during parsing) are expanded if they are small enough,
 *    as governed by the distinct_group_expansion_limit option. Groups too big to
 *    expand survive into the search, where DistinctEqualitySimplifier uses them.
 *
 * The two belong together: phase 1 decides *whether* something can be a group,
 * phase 2 applies the single size policy to all groups alike.
 */
class DistinctGroupExpansion {
public:
  DistinctGroupExpansion(unsigned expandUpToSize) : _expandUpToSize(expandUpToSize) {}

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  Formula* expand(Stack<unsigned>& constants);
  Formula* expandTerms(Stack<TermList>& terms, TermList sort);
  Formula* expandLiteral(Literal* lit);
private:
  bool eliminateDistinctPredicates(UnitList*& units);
  bool expandGroups(UnitList*& units);
  Formula* processTopLevel(Formula* f, Unit* premise);

  unsigned _expandUpToSize;
};


}
#endif
