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

SubstIterator HOLUnification::unifiers(TermList t1, int index1, TermList t2, int index2, RobSubstitution* sub, bool topLevelCheck)
{
  CALL("HOLUnification::unifiers");

  // TODO dummy implementation
  return SubstIterator::getEmpty();
}

SubstIterator HOLUnification::postprocess(RobSubstitution* sub)
{
  CALL("HOLUnification::postprocess");
 
  cout << *sub << endl;

  // TODO dummy implementation
  return pvi(getSingletonIterator(sub));  
}

bool HOLUnification::associate(unsigned specialVar, TermList node, bool splittable, RobSubstitution* sub)
{
  CALL("HOLUnification::associate");

  TermList query(specialVar, /* special */ true);
  return unifyTreeTerms(query, QUERY_BANK, node, NORM_RESULT_BANK, splittable, sub);
}

bool HOLUnification::unifyTreeTerms(TermList t1, unsigned bank1, TermList t2, unsigned bank2, bool splittable,  RobSubstitution* sub){
  CALL("HOLUnification::unifyWithPlaceholders");

  return unify(TermSpec(t1,bank1), TermSpec(t2,bank2), splittable, sub);  
}

// TODO consider aadding a check for loose De Bruijn indices
// see E prover code by petar /TERMS/cte_fixpoint_unif.c
#define DEBUG_FP_UNIFY(LVL, ...) if (LVL <= 1) DBG(__VA_ARGS__)
HOLUnification::OracleResult HOLUnification::fixpointUnify(VarSpec var, const TermSpec& t, RobSubstitution* sub)
{
  CALL("HOLUnification::fixpointUnify");

  struct TermSpecFP {
    TermSpec t;
    bool underFlex;
  };

  bool tIsLambda = t.toTerm(*sub).whnf().isLambdaTerm();
  VarSpec toFind = sub->root(var);
  TermSpec ts = sub->derefBound(t).clone();
  if(ts.isVar()) {
    DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
    sub->bind(toFind, ts.clone());
    return OracleResult::SUCCESS;
  }


  typedef DHSet<VarSpec, VarSpec::Hash1, VarSpec::Hash2> EncounterStore;
  Recycled<EncounterStore> encountered;
  Recycled<Stack<TermSpecFP>> todo;
  todo->push(TermSpecFP { .t = t.clone(), .underFlex = false  });

  while (todo->isNonEmpty()){
    auto ts = todo->pop();


    TermSpec head;
    Stack<TermSpec> args;

    ts.t.headAndArgs(head, args);

    if (head.isVar()) {
      VarSpec tvar = sub->root(head.varSpec());
      if(tvar == toFind) {
        if(ts.underFlex || (tIsLambda && args.size())){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;          
        }
      } else if(!encountered->find(tvar)) {
        TermSpec dtvar = sub->derefBound(TermSpec(tvar)).clone();
        if(!dtvar.isVar()) {
          encountered->insert(tvar);
          todo->push(TermSpecFP { .t = std::move(dtvar), .underFlex = ts.underFlex  });
        }
      }

    } else {
      // this is a bit nasty.
      // if we know that the original variable is a term var
      // we wouldn't need to iterate through sort arguments
      // sadly, that is not the case ...
      for(auto c : head.allArgs()){
        todo->push(TermSpecFP { .t = c.clone(), .underFlex = ts.underFlex} );
      }
    }

    bool argsUnderFlex = head.isVar() ? true : ts.underFlex;

    for(unsigned i = 0; i < args.size(); i++){
      // TODO double iteration over args. Once here and once in TermSpec::headAndArgs(...)
      todo->push(TermSpecFP { args[i].clone(), .underFlex = argsUnderFlex} );      
    }
  }

  DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
  sub->bind(toFind, ts.clone());
  return OracleResult::SUCCESS;
}


#define DEBUG_UNIFY(LVL, ...) if (LVL <= 2) DBG(__VA_ARGS__)
bool HOLUnification::unify(TermSpec t1, TermSpec t2, bool splittable, RobSubstitution* sub)
{
  CALL("HOLUnification::unify");

  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, (splittable ? "" : "{NS}"), ")")
  if(t1 == t2) {
    return true;
  }

  auto impl = [&]() -> bool {

    TermList t1t = t1.toTerm(*sub);
    TermList t1thead = t1t.head();

    // Node term and query term must have the same type. Hence we do not
    // to check for type of query. We can rely on the !splittable check 
    if(!t1t.isVar() && (t1thead.isVar() || t1thead.isLambdaTerm() || !splittable)) {
      // create top level constraint
      sub->pushConstraint(UnificationConstraint(t1.clone(), t2.clone()));
      return true;
    }

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

    auto sortCheck = [](auto& t) {
      return
        env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION &&
        (t.isNormalVar() || t.isArrowSort() || t.isBoolSort());
    };

    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto& dt1 = x.lhs().deref(sub);
      auto& dt2 = x.rhs().deref(sub);
      DEBUG_UNIFY(2, ".unify(", dt1, ",", dt2, ")")

      if (dt1 == dt2) {
        // do nothing
      } else if(dt1.isVar()) {
        auto res = fixpointUnify(dt1.varSpec(), dt2, sub);
        if(res == OracleResult::FAILURE) return false;
        if(res == OracleResult::OUT_OF_FRAGMENT)
          sub->pushConstraint(UnificationConstraint(dt1.clone(), dt2.clone()));

      } else if(dt2.isVar()) {
        auto res = fixpointUnify(dt2.varSpec(), dt1, sub);        
        if(res == OracleResult::FAILURE) return false;
        if(res == OracleResult::OUT_OF_FRAGMENT)
          sub->pushConstraint(UnificationConstraint(dt2.clone(), dt1.clone()));

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        if(dt1.isApplication()){
          ASS(dt2.isApplication());
          TermSpec dt1s1 = dt1.typeArg(0);
          TermSpec dt2s1 = dt2.typeArg(0);
          TermSpec dt1t2 = dt1.termArg(1);
          TermSpec dt2t2 = dt2.termArg(1);
          TermList dt1t2head = dt1t2.head(sub);
          TermList dt2t2head = dt2t2.head(sub);          
          pushTodo(UnificationConstraint(dt1s1.clone(), dt2s1.clone()));
          pushTodo(UnificationConstraint(dt1.typeArg(1).clone(), dt2.typeArg(1).clone()));
          pushTodo(UnificationConstraint(dt1.termArg(0).clone(), dt2.termArg(0).clone()));

          // Not sure the logic below is right. Things get very complicated because
          // the sorts can be special variables. I think what we have below is an 
          // over approximation, but I am not 100%
          if(dt1t2.isVar() || dt2t2.isVar()){
            // if either is a variable let fixpoint unification decide 
            // whether to create a constraint or to bind
            pushTodo(UnificationConstraint(std::move(dt1t2), std::move(dt2t2)));
          } else if(sortCheck(dt1s1) || dt1t2head.isVar() || dt1t2head.isLambdaTerm() ||
                    sortCheck(dt2s1) || dt2t2head.isVar() || dt2t2head.isLambdaTerm() ) {
            sub->pushConstraint(UnificationConstraint(dt1t2.clone(), dt2t2.clone()));
          } else {
            pushTodo(UnificationConstraint(std::move(dt1t2), std::move(dt2t2)));
          }
        } else {
          for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
            pushTodo(UnificationConstraint(std::move(c.first), std::move(c.second)));
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