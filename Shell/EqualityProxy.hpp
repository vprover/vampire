/**
 * @file EqualityProxy.hpp
 * Defines class EqualityProxy.
 */


#ifndef __EqualityProxy__
#define __EqualityProxy__

#include "Forwards.hpp"

#include "Lib/Array.hpp"

#include "Kernel/Term.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;


/**
 * Applies the equality proxy transformation to the problem.
 * It works as follows:
 * <ol>
 *   <li>all literals x = y are replaced by E(x,y);</li>
 *   <li>if _option is in {R,RS,RST,RSTC} all literals s=t are replaced by E(s,t);</li>
 *   <li>all literals s != t are replaced by ~E(s,t);</li>
 *   <li>the clause E(x,x) is added;</li>
 *   <li>if _option is in {RS,RST,RSTC} the symmetry clause ~E(x,y) \/ E(y,x) is added;</li>
 *   <li>if _option is in {RST,RSTC} the transitivity clause
 *       ~E(x,y) \/ ~E(y,z) \/ E(x,z) is added;</li>
 *   <li>if _option==RSTC the congruence clauses are added:
 *   	<ul>
 *       <li> ~E(x1,y1) \/ ... \/ ~E(xN,yN) \/ ~p(x1,...,xN) \/ p(y1,...,yN)
 *       	for all predicates p except equality and E </li>
 *       <li> ~E(x1,y1) \/ ... \/ ~E(xN,yN) \/ E(f(x1,...,xN),f(y1,...,yN))
 *       	for all non-constant functions f </li>
 *      </ul>
 *   </li>
 *   <li>if _option is not in {R,RS,RST} the clause ~E(x,y) \/ x = y is added;</li>
 * </ol>
 */
class EqualityProxy
{
public:
  EqualityProxy();
  EqualityProxy(Options::EqualityProxy opt);

  void apply(Problem& prb);
  void apply(UnitList*& units);
private:
  void init();
  void addLocalAxioms(UnitList*& units, unsigned sort);
  void addAxioms(UnitList*& units);
  void addCongruenceAxioms(UnitList*& units);
  bool getArgumentEqualityLiterals(unsigned cnt, LiteralStack& lits, Stack<TermList>& vars1,
      Stack<TermList>& vars2, BaseType* symbolType, bool skipSortsWithoutEquality);
  Clause* apply(Clause* cl);
  Literal* apply(Literal* lit);
  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1);
  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1, unsigned sort);

  bool haveProxyPredicate(unsigned sort) const;
  unsigned getProxyPredicate(unsigned sort);

  Options::EqualityProxy _opt;

  /**
   * Proxy predicate numbers for each sort. If element on at the position
   * of a predicate is zero, it means the proxy predicate for that sort wasn't
   * added yet.
   */
  static ZIArray<unsigned> s_proxyPredicates;
  bool _rst;
};

};

#endif /* __EqualityProxy__ */
