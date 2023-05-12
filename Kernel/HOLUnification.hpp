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
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __HOLUnification__
#define __HOLUnification__

#if VHOL

#include "Forwards.hpp"

#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {


class HOLUnification {

  bool unifyFirstOrderStructure(TermList t1, TermList t2, bool splittable, RobSubstitutionTL* sub);

  // TODO if we implement solid fragment, this will not work...
  enum OracleResult
  {
    SUCCESS=1,
    FAILURE=2,
    OUT_OF_FRAGMENT=3
  };  

  static OracleResult fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub);

  using UnificationConstraint = UnificationConstraint<TermList,VarBank>;

  class HOLConstraint : public UnificationConstraint
  {
  private:
    TermList _t1head;
    TermList _t2head;
  public:

    HOLConstraint(){} // dummy constructor required for use in SkipList
    HOLConstraint(TermList t1, TermList t2) : UnificationConstraint(t1,t2), 
      _t1head(t1.head()), _t2head(t2.head()) {
      ASS(!_t1head.isLambdaTerm() && !_t2head.isLambdaTerm()); // terms must be in whnf
    }
    CLASS_NAME(HOLConstraint)
    USE_ALLOCATOR(HOLConstraint)

    bool flexFlex()   const { return _t1head.isVar() && _t2head.isVar(); }
    bool rigidRigid() const { return _t1head.isTerm() && _t2head.isTerm(); }
    bool flexRigid()  const { return (_t1head.isVar() && !_t2head.isVar())  || (_t2head.isVar() && !_t1head.isVar()); }

    TermList lhsHead() const { return _t1head; }
    TermList rhsHead() const { return _t2head; }

    TermList sort() const {
      CALL("HOLConstraint::sort()");
      ASS(lhs().isTerm() || rhs().isTerm());      
      if(lhs().isTerm())
      { return SortHelper::getResultSort(lhs().term()); }
      return SortHelper::getResultSort(rhs().term());      
    }

    UnificationConstraint constraint() { return UnificationConstraint(lhs(),rhs()); }
  };

  class HigherOrderUnifiersIt;

public:
  HOLUnification() { }

  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub);
  SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitutionTL*);

  void initSub(RobSubstitutionTL* sub) const { }

  // method used to decide whether to return all children of a node during tree
  // traversal or only the children with same top
  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
