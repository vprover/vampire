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
#include "Kernel/ApplicativeHelper.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

SubstIterator HOLUnification::unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck)
{
  CALL("HOLUnification::unifiers");

  // TODO dummy implementation
  return SubstIterator::getEmpty();
}

SubstIterator HOLUnification::postprocess(RobSubstitutionTL* sub)
{
  CALL("HOLUnification::postprocess");
 
  // We could carry out a fix point iteration here
  // but it is slighly involved and I am not sure that it is worth it.
  // will leave for now.

  // TODO dummy implementation
  return pvi(getSingletonIterator(sub));
}

bool HOLUnification::associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::associate");

  TermList query(specialVar, /* special */ true);
  return unifyTreeTerms(query, node, splittable, sub);
}


// TODO consider adding a check for loose De Bruijn indices
// see E prover code by petar /TERMS/cte_fixpoint_unif.c
#define DEBUG_FP_UNIFY(LVL, ...) if (LVL <= 1) DBG(__VA_ARGS__)
HOLUnification::OracleResult HOLUnification::fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::fixpointUnify");
  ASS(var.isVar());

  struct TermListFP {
    TermList t;
    bool underFlex;
  };

  bool tIsLambda = t.whnfDeref(sub).isLambdaTerm();
  TermList toFind = sub->root(var);
  TermList ts = sub->derefBound(t); // TODO do we even need this derefBound? Shouldn't t already be dereferenced???
  if(ts.isVar()) {
    DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
    sub->bind(toFind, ts);
    return OracleResult::SUCCESS;
  }


  Recycled<Stack<TermListFP>> todo;
  todo->push(TermListFP { .t = t, .underFlex = false  });

  while (todo->isNonEmpty()){
    auto ts = todo->pop();
    auto term = ts.t.whnfDeref(sub);

    // TODO consider adding an encountered store similar to first-order occurs check...

    TermList head;
    TermStack args;

    ApplicativeHelper::getHeadAndArgs(term, head, args);

    if (head.isVar()) {
      if(head == toFind) {
        if(ts.underFlex || (tIsLambda && args.size())){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;          
        }
      }
    } else if (head.isLambdaTerm()) {
      ASS(!args.size()); // if we had args, term wouldnt be in whnf
      todo->push(TermListFP { head.lambdaBody(), .underFlex = ts.underFlex} );      
    }


    bool argsUnderFlex = head.isVar() ? true : ts.underFlex;

    for(unsigned i = 0; i < args.size(); i++){
      todo->push(TermListFP { args[i], .underFlex = argsUnderFlex} );      
    }
  }

  DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
  sub->bind(toFind, ts);
  return OracleResult::SUCCESS;
}


#define DEBUG_UNIFY(LVL, ...) if (LVL <= 2) DBG(__VA_ARGS__)
bool HOLUnification::unifyTreeTerms(TermList t1, TermList t2, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::unifyTreeTerms");

  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, (splittable ? "" : "{NS}"), ")")
  if(sub->sameTermContent(t1,t2)) {
    return true;
  }

  auto impl = [&]() -> bool {

    ASS(t1.isSpecialVar());
    t1 = sub->derefBound(t1);    

    if( (t1.isTerm() && t1.term()->isSort()) || 
        (t2.isTerm() && t2.term()->isSort()) ) {
      return sub->unify(t1,t2); // sorts can be unified by standard algo
    }

    TermList t1thead = sub->derefBound(t1.head());

    // Node term and query term must have the same type. Hence we do not
    // check type of query. We can rely on the !splittable check 
    // TODO, logic is a little off here. A node can be non-splittanle, but on
    // apply a substitution to the term it can become splittable
    if(!t1.isVar() && (t1thead.isVar() || t1thead.isLambdaTerm() || !splittable)) {
      // create top level constraint
      sub->pushConstraint(UnificationConstraint(t1, t2));
      return true;
    }

    Recycled<Stack<UnificationConstraint>> toDo;
    toDo->push(UnificationConstraint(t1, t2));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint>> encountered;

    auto pushTodo = [&](auto pair) {
      if (!encountered->find(pair)) {
        encountered->insert(pair);
        toDo->push(pair);
      }
    };

    auto sortCheck = [](auto& t) {
      return
        env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION &&
        (t.isOrdinaryVar() || t.isArrowSort() || t.isBoolSort());
    };

    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      TermList dt1 = sub->derefBound(x.lhs());
      TermList dt2 = sub->derefBound(x.rhs());
      DEBUG_UNIFY(2, ".unify(", dt1, ",", dt2, ")")

      if (sub->sameTermContent(dt1, dt2)) {
        // do nothing
      } else if(dt1.isVar()) {
        auto res = fixpointUnify(dt1, dt2, sub);
        if(res == OracleResult::FAILURE) return false;
        if(res == OracleResult::OUT_OF_FRAGMENT)
          sub->pushConstraint(UnificationConstraint(dt1, dt2));

      } else if(dt2.isVar()) {
        auto res = fixpointUnify(dt2, dt1, sub);        
        if(res == OracleResult::FAILURE) return false;
        if(res == OracleResult::OUT_OF_FRAGMENT)
          sub->pushConstraint(UnificationConstraint(dt2, dt1));

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.term()->functor() == dt2.term()->functor()) {
        
        if(dt1.isApplication()){
          ASS(dt2.isApplication());
          TermList dt1s1 = dt1.term()->typeArg(0);
          TermList dt2s1 = dt2.term()->typeArg(0);
          TermList dt1t2 = dt1.term()->termArg(1);
          TermList dt2t2 = dt2.term()->termArg(1);
          TermList dt1t2head = sub->derefBound(dt1t2.head());
          TermList dt2t2head = sub->derefBound(dt2t2.head());          

          pushTodo(UnificationConstraint(dt1.term()->termArg(0), dt2.term()->termArg(0)));

          // Not sure the logic below is right. Things get very complicated because
          // the sorts can be special variables. I think what we have below is an 
          // over approximation, but I am not 100%
          if(!dt1t2.isVar() && !dt2t2.isVar() &&  // if either is a variable let fixpoint unification decide whether to create a constraint or to bind
             (sortCheck(dt1s1) || dt1t2head.isVar() || dt1t2head.isLambdaTerm() ||
              sortCheck(dt2s1) || dt2t2head.isVar() || dt2t2head.isLambdaTerm() )) {
            sub->pushConstraint(UnificationConstraint(dt1t2, dt2t2));
          } else {
            pushTodo(UnificationConstraint(dt1t2, dt2t2));
          }
        } else {
          for (unsigned i = 0; i < dt1.term()->arity(); i++) {
            // must be a sort
            bool unifySort = sub->unify(dt1.nthArg(i), dt2.nthArg(i));
            if(!unifySort) return false; // failed sort unification            
          }
        }

      } else {
        // head symbol clash at first-order position
        // can be no unifier fail
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