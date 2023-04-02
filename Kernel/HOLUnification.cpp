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

#if VHOL

#include "Kernel/HOLUnification.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

SubstIterator HOLUnification::unifiers(TermList t1, int index1, TermList t2, int index2, RobSubstitution* sub, bool topLevelCheck)
{
  CALL("HOLUnification::unifiers");

  // TODO dummy implementation
  return SubstIterator::getEmpty();
}

SubstIterator HOLUnification::postprocess(RobSubstitution* sub, TermList t)
{
  CALL("HOLUnification::postprocess");
  ASS(!_origQuery.isEmpty());

  // TODO dummy implementation
  return pvi(getSingletonIterator(sub));  
}

bool HOLUnification::associate(unsigned specialVar, TermList node, BacktrackData& bd, RobSubstitution* sub)
{
  CALL("HOLUnification::associate");
  TermList query(specialVar, /* special */ true);
  return unifyWithPlaceholders(query, QUERY_BANK, node, NORM_RESULT_BANK, sub);
}

bool HOLUnification::unifyWithPlaceholders(TermList t1, unsigned bank1, TermList t2, unsigned bank2, RobSubstitution* sub){
  CALL("HOLUnification::unifyWithPlaceholders");

  return unify(TermSpec(t1,bank1), TermSpec(t2,bank2), sub);  
}

#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
bool HOLUnification::unify(TermSpec t1, TermSpec t2, RobSubstitution* sub)
{
  CALL("HOLUnification::unify");

  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, ")")
  if(t1 == t2) {
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnificationConstraint>> toDo;
    toDo->push(UnificationConstraint(t1.clone(), t2.clone()));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint>> encountered;

    auto pushTodo = [&](auto pair) {
        if (!encountered->find(pair)) {
          encountered->insert(pair.clone());
          toDo->push(std::move(pair));
        }
    };

    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto& dt1 = x.lhs().deref(sub);
      auto& dt2 = x.rhs().deref(sub);

      if (dt1 == dt2 || dt1.isPlaceholder() || dt2.isPlaceholder()) {
        // do nothing
        // we want unification to pass in these cases
      } else if(dt1.isVar() && !sub->occurs(dt1.varSpec(), dt2)) {
        sub->bind(dt1.varSpec(), dt2.clone());
      } else if(dt2.isVar() && !sub->occurs(dt2.varSpec(), dt1)) {
        sub->bind(dt2.varSpec(), dt1.clone());
      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
          pushTodo(UnificationConstraint(std::move(c.first), std::move(c.second)));
        }

      } else {
        return false;
      }
    }
    return true;
  };

  BacktrackData localBD;
  sub->bdRecord(localBD);
  bool success = impl();
  sub->bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(sub->bdIsRecording()) {
      sub->bdCommit(localBD);
    }
    localBD.drop();
  }

  return success;
}

}

}

#endif