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

#ifndef __EqualityProxyMono__
#define __EqualityProxyMono__

#include "Forwards.hpp"

#include "Lib/Array.hpp"

#include "Kernel/Term.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Kernel;

// Monomorphic version of equality proxy transformation.
// When working with a monomorphic problem, both the poly and the mono
// versions can be used. Poly is default. 

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
 */
class EqualityProxyMono
{
public:
  EqualityProxyMono(Options::EqualityProxy opt);

  void apply(Problem& prb);
  void apply(UnitList*& units);
  Clause* apply(Clause* cl);
private:
  void addLocalAxioms(UnitList*& units, TermList sort);
  void addAxioms(UnitList*& units);
  void addCongruenceAxioms(UnitList*& units);
  bool getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits, Lib::Stack<TermList>& vars1,
      Lib::Stack<TermList>& vars2, OperatorType* symbolType, bool skipSortsWithoutEquality);
  Literal* apply(Literal* lit);
  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort);

  bool haveProxyPredicate(TermList sort) const;
  unsigned getProxyPredicate(TermList sort);
  Clause* createEqProxyAxiom(const LiteralStack& literalIt);

  /** the equality proxy option value, passed in the constructor */
  Options::EqualityProxy _opt;

  /**
   * Proxy predicate numbers for each sort (which can be a complex term, even in mono - think arrays)
   * but must be ground (and shared).
   */
  static Lib::DHMap<TermList, unsigned> s_proxyPredicates;
  /** equality proxy predicate sorts */
  static Lib::DHMap<unsigned,TermList> s_proxyPredicateSorts;
  /** array of proxy definitions E(x,y) <=> x = y  */
  static Lib::DHMap<TermList, Unit*> s_proxyPremises;
};

};

#endif /* __EqualityProxy__ */
