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

#include "Lib/Array.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/OperatorType.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

// Polymorphic version of equality proxy transformation.
// When working with a monomorphic problem, both the poly and the mono
// versions can be used. Poly is default. 
// The one exception is when using instGen calculus which has not 
// been tested with polymrphism. In this case, mono version must be used

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
class EqualityProxy
{
public:
  CLASS_NAME(EqualityProxy);
  USE_ALLOCATOR(EqualityProxy);

  EqualityProxy(Options::EqualityProxy opt);

  void apply(Problem& prb);
  void apply(UnitList*& units);
  Clause* apply(Clause* cl);
private:
  void addLocalAxioms(UnitList*& units);
  void addAxioms(UnitList*& units);
  void addCongruenceAxioms(UnitList*& units);
  void getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits, Stack<TermList>& vars1,
      Stack<TermList>& vars2, OperatorType* symbolType);
  Literal* apply(Literal* lit);
  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, TermList sort);

  unsigned getProxyPredicate();
  Clause* createEqProxyAxiom(const LiteralStack& literalIt);

  /** the equality proxy option value, passed in the constructor */
  Options::EqualityProxy _opt;

  bool _addedPred;
  unsigned _proxyPredicate;

  /** array of proxy definitions E(x,y) <=> x = y  */
  //static ZIArray<Unit*> s_proxyPremises;
  Unit* _defUnit;

};

};

#endif /* __EqualityProxy__ */
