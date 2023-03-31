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
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {

// TODO moce somewhere more suitable
class RobUnification { 
public:

  // to be used for tree calls
  bool associate(unsigned specialVar, TermList node, BacktrackData& bd, RobSubstitution* sub)
  {
    CALL("RobUnification::associate");
    TermList query(specialVar, /* special */ true);
    return sub->unify(query, QUERY_BANK, node, NORM_RESULT_BANK);
  }

  // To be used for non-tree calls. Return an iterator instead of bool
  // to fit HOL interface
  SubstIterator unifiers(TermList t1, int index1, TermList t2, int index2, bool topLevelCheck = false){
    CALL("RobUnification::unifiers");     

    static RobSubstitution subst;
    subst.reset();

    if(subst.unify(t1, index1, t2, index2)){
      return pvi(getSingletonIterator(&subst));
    }
    return SubstIterator::getEmpty();
  }

  // function is called when in the leaf of a substitution tree 
  // during unification. t is the term stored in the leaf
  SubstIterator postprocess(RobSubstitution* sub, TermList t){
    CALL("RobUnification::postprocess");     
    
    // sub is a unifier of query and leaf term t, return it
    return pvi(getSingletonIterator(sub));
  }

  bool usesUwa() const { return false; }
};


class HOLUnification {
  // when this class is used for tree unification the field
  // below holds the original query before higher-order subterms have
  // been replaced by placeholders
  TermList _origQuery; 
  bool unify(TermSpec t1, TermSpec t2, RobSubstitution* sub);

public:
  HOLUnification() {  _origQuery.makeEmpty(); }
  HOLUnification(TermList query) :  _origQuery(query) {}

  bool unifyWithPlaceholders(TermList t1, unsigned bank1, TermList t2, unsigned bank2, RobSubstitution* sub);
  bool associate(unsigned specialVar, TermList node, BacktrackData& bd, RobSubstitution* sub);
  SubstIterator unifiers(TermList t1, int index1, TermList t2, int index2, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitution*, TermList t);

  // method used to decide whether to return all children of a node during tree
  // traversal or only the children with same top
  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
