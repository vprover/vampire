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
 * @file EqualityProxy.hpp
 * Defines class EqualityProxy implementing the equality proxy transformation.
 */

#ifndef __EqualityProxy__
#define __EqualityProxy__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/OperatorType.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Applies the equality proxy transformation to the problem.
 * It works as follows:
 * <ol>
 *   <li>All literals s=t are replaced by E(s,t);</li>
 *   <li>all literals s != t are replaced by ~E(s,t);</li>
 *   <li>the clause E(x,x) is added;</li>
 *   <li>if _option is in {EP_RS,EP_RST,EP_RSTC} the symmetry clause ~E(x,y) \/ E(y,x) is added;</li>
 *   <li>if _option is in {EP_RST,EP_RSTC} the transitivity clause
 *       ~E(x,y) \/ ~E(y,z) \/ E(x,z) is added;</li>
 *   <li>if _option == EP_RSTC the congruence clauses are added:
 *   	<ul>
 *       <li> ~E(x1,y1) \/ ... \/ ~E(xN,yN) \/ ~p(x1,...,xN) \/ p(y1,...,yN)
 *       	for all predicates p except equality and E </li>
 *       <li> ~E(x1,y1) \/ ... \/ ~E(xN,yN) \/ E(f(x1,...,xN),f(y1,...,yN))
 *       	for all non-constant functions f </li>
 *      </ul>
 *   </li>
 * </ol>
 *
 * There are two variants of the transformation, selected by the @b poly flag
 * of the constructor:
 * <ul>
 *   <li>the monomorphic one introduces one proxy predicate E_sigma : (sigma*sigma) > $o
 *       per sort sigma on which equality is actually used. Every sort met must be ground;</li>
 *   <li>the polymorphic one introduces a single proxy predicate
 *       E : !>[X]:(X*X) > $o, which also copes with equalities between terms of a
 *       variable sort, at the price of turning the problem polymorphic.</li>
 * </ul>
 * Only a problem which is polymorphic already should be given the polymorphic variant.
 */
class EqualityProxy
{
public:
  EqualityProxy(Options::EqualityProxy opt, bool poly);

  void apply(Problem& prb);
  void apply(UnitList*& units);
  Clause* apply(Clause* cl);
private:
  void addLocalAxioms(UnitList*& units, TermList sort);
  void addAxioms(UnitList*& units);
  void addCongruenceAxioms(UnitList*& units);
  bool getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits, Stack<TermList>& vars1,
      Stack<TermList>& vars2, OperatorType* symbolType, bool skipSortsWithoutEquality);
  Literal* apply(Literal* lit);
  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort);

  bool haveProxyPredicate(TermList sort) const;
  unsigned getProxyPredicate(TermList sort);
  Unit* premiseFor(Literal* proxyLit) const;
  Clause* createEqProxyAxiom(const LiteralStack& literalIt);

  /** the equality proxy option value, passed in the constructor */
  Options::EqualityProxy _opt;
  /** use the single polymorphic proxy predicate instead of one predicate per sort */
  bool _poly;

  /** the polymorphic proxy predicate; only meaningful once _defUnit is set */
  unsigned _proxyPredicate;
  /** the definition E(x,y) <=> x = y of the polymorphic proxy predicate (and the "have it already" flag) */
  Unit* _defUnit;

  /**
   * Proxy predicate numbers for each sort (which can be a complex term, even in mono - think arrays)
   * but must be ground (and shared).
   *
   * The id-based hashes matter: this map gets enumerated to emit the local axioms, and with
   * the default (address-based) ones the axioms would come out in a different order in every run.
   */
  DHMap<TermList, unsigned, SharedTermListHash, SharedTermListHash2> _proxyPredicates;
  /** equality proxy predicate sorts */
  DHMap<unsigned, TermList> _proxyPredicateSorts;
  /** the definitions E_sigma(x,y) <=> x = y, indexed by the sort sigma */
  DHMap<TermList, Unit*, SharedTermListHash, SharedTermListHash2> _proxyPremises;
};

};

#endif /* __EqualityProxy__ */
