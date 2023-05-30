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
 * @file HOLUnification.hpp
 * Defines class HOLUnification.
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

#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {


class HOLUnification {
  // when this class is used for tree unification the field
  // below holds the original query before higher-order subterms have
  // been replaced by placeholders
  TermList _origQuery;
  TermList _origQuerySort;
  bool _funcExt;

  bool unifyWithPlaceholders(TermList t1, TermList t2, RobSubstitutionTL* sub);

  // TODO if we implement solid fragment, this will not work...
  enum OracleResult
  {
    SUCCESS=1,
    FAILURE=2,
    OUT_OF_FRAGMENT=3
  };  

  static OracleResult fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub);

  using UnifConstraint = UnificationConstraint<TermList,VarBank>;

  class HOLConstraint : public UnifConstraint
  {
  private:
    TermList _t1head;
    TermList _t2head;
  public:

    HOLConstraint(){} // dummy constructor required for use in SkipList
    HOLConstraint(TermList t1, TermList t2) : UnifConstraint(t1,t2), 
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

    UnifConstraint constraint() { return UnifConstraint(lhs(),rhs()); }
  };

  inline bool sortCheck(TermList sort, bool topLevel = false){
    CALL("HOLUnification::sortCheck");
    return
      _funcExt &&
      (sort.isOrdinaryVar() || sort.isArrowSort() || (sort.isBoolSort() && !topLevel));    
  }

  class HigherOrderUnifiersIt;
  class HigherOrderUnifiersItWrapper;

public:

  HOLUnification() : _funcExt( env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION)
  {}

  HOLUnification(TypedTermList query) : 
  _funcExt( env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION) {
    TypedTermList t = ToBank(QUERY_BANK).toBank(query);
    _origQuery = t;
    _origQuerySort = t.sort();
  }

  bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub);
  SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitutionTL*, TermList t, TermList sort);

  void initSub(RobSubstitutionTL* sub) const { }

  // method used to decide whether to return all children of a node during tree
  // traversal or only the children with same top
  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
