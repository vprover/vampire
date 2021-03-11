
/*
 * File LaKbo.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LaKbo.hpp
 *
 * Defines a Knuth-Bendix Ordering for linear arithmetic. This ignores numeral multiplications,
 * (i.e. it considers terms t and nt where n is a numeral as equaivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __LINEAR_ARITHMETIC_KBO__
#define __LINEAR_ARITHMETIC_KBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Kernel/KBO.hpp"

#include "Ordering.hpp"
#include "Lib/Map.hpp"
// #include "Kernel/PolynomialNormalizer.hpp"

namespace Kernel {

using namespace Lib;

class LaKbo 
  : public KBO
{
public:
  CLASS_NAME(LaKbo);
  USE_ALLOCATOR(LaKbo);

  LaKbo(LaKbo&& kbo) = default;
  LaKbo& operator=(LaKbo&& kbo) = default;
  explicit LaKbo(KBO kbo);

  static LaKbo testKBO();

  virtual ~LaKbo() {}

  Result comparePredicates(Literal* l1,Literal* l2) const final override;
  Result compare(TermList, TermList) const final override;
  Result compare(Literal* l1, Literal* l2) const final override { return PrecedenceOrdering::compare(l1, l2); }

  void show(ostream& out) const final override;
  Comparison compareFunctors(unsigned fun1, unsigned fun2) const override;
protected:
  int symbolWeight(Term* t) const;

private:
  enum VarCondition {
    Equal,
    LeftPlus,
    RightPlus,
    BothPlus,
  };

  struct TraversalResult 
  {
    static TraversalResult initial();
    int weight_balance;
    Map<unsigned, int> var_balances;
    Stack<unsigned> vars;
    Result side_condition;
    void addVarBalance(unsigned var,int amount);
    VarCondition varCondition() const;
  };

  Result toOrdering(TraversalResult const& res) const;
  void traverse(TraversalResult& res, TermList  t1, TermList t2) const;
  void traverse(TraversalResult& res, TermList* tt, int factor ) const;
  void traverse(TraversalResult& res, TermList  t , int factor ) const;
  template<class F> void traverse(TraversalResult& res, TermList* tt, int factor, F fun) const;
  template<class F> void traverse(TraversalResult& res, TermList  t , int factor, F fun) const;
  void traverseLex(TraversalResult& res, TermList* tt1, TermList* tt2) const;
  void traverseSubterm(TraversalResult& res, Term* t, unsigned v, bool varRhs) const;
  void traverseAC(TraversalResult& res, Term* t1, Term* t2) const;
  TermList dropNumeralMultiplications(LaKbo::TraversalResult& res,  TermList t) const;

};

} // namespace Kernel

#endif // __LINEAR_ARITHMETIC_KBO__
