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

#include "Lib/SkipList.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

class HOLUnification::HigherOrderUnifiersIt: public IteratorCore<RobSubstitutionTL*> {
public:
  HigherOrderUnifiersIt(RobSubstitutionTL* subst) :
    _returnInitial(false),  _used(false), _subst(subst){
    ASS(!_subst->bdIsRecording());
    _subst->bdRecord(_initData);

    // move constraints from to priority queue
    // will be undone when hasNext() return false
    while(!_subst->emptyConstraints()){
      auto con = _subst->popConstraint();
      TermList lhs = con.lhs();
      TermList rhs = con.rhs();
      lhs = lhs.whnfDeref(_subst);
      rhs = rhs.whnfDeref(_subst);
      auto higherOrderCon = HOLConstraint(lhs,rhs);
      if(higherOrderCon.rigidRigid()){
        // if one of the pairs is rigid rigid and is of functional sort
        // don't do any higher-order unification. Instead let functional extensionality
        // inferences such as ArgCong and NegExt do their thing
        TermList sort = higherOrderCon.sort();
        if(sort.isArrowSort() || sort.isOrdinaryVar()){
          _returnInitial = true;
          break;
        }
      }
      addToUnifPairs(higherOrderCon,_initData);
    }

    _subst->bdDone();
    if(_returnInitial){
      _initData.backtrack();
    }
  }
  
  ~HigherOrderUnifiersIt() {
    CALL("HOLUnification::HigherOrderUnifiersIt::~HigherOrderUnifiersIt");
    ASS(_unifPairs.isEmpty());
  }

  bool hasNext() {
    CALL("HOLUnification::HigherOrderUnifiersIt::hasNext");
    
    if(_returnInitial){
      if(!_used){
        _used = true;
        return _used;
      }
      return false;
    }

    //dummy
    return true;
  }

  RobSubstitutionTL* next() {
    CALL("HOLUnification::HigherOrderUnifiersIt::next");

    return _subst;
  }

  void addToUnifPairs(HOLConstraint con, BacktrackData& bd){
    CALL("HigherOrderUnifiersIt::addToUnifPairs");

    _unifPairs.insert(con);
    bd.addClosure([&](){ _unifPairs.remove(con); });
  }

private:

  class HOLCnstComp
  {
  public:
    inline
    static Comparison compare(const HOLConstraint& hc1, const HOLConstraint& hc2)
    {
      CALL("HOLUnification::HOLCnstComp::compare");

      auto compareTerms = [](TermList t1, TermList t2){
        if(t1.isVar()){
          if(t2.isVar()){
            return (t1.var() < t2.var()) ? LESS : (t1.var() > t2.var())? GREATER : EQUAL;
          }
          return LESS;
        } else if(t2.isVar()){
          return GREATER;
        }
        
        unsigned id1 = t1.term()->getId();
        unsigned id2 = t2.term()->getId();        

        return (id1<id2)? LESS : (id1>id2)? GREATER : EQUAL;
      };

      if(hc1.rigidRigid() && !hc2.rigidRigid()){
        return LESS;
      } else if (hc2.rigidRigid() && !hc1.rigidRigid()){
        return GREATER;
      } else if (hc1.flexRigid() && hc2.flexFlex()){
        return LESS;
      } else if (hc2.flexRigid() && hc1.flexFlex()){
        return GREATER;
      } 
     
      auto res = compareTerms(hc1.lhs(), hc2.lhs());
      if(res == EQUAL){
        res = compareTerms(hc1.rhs(), hc2.rhs());
      }
      return res;
    }
  };

  bool _returnInitial;
  bool _used;
  BacktrackData _initData;
  SkipList<HOLConstraint,HOLCnstComp> _unifPairs;
  RobSubstitutionTL* _subst;
};

SubstIterator HOLUnification::unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck)
{
  CALL("HOLUnification::unifiers");

  bool splittable = true;
  if(!ApplicativeHelper::splittable(t1) || !ApplicativeHelper::splittable(t2)){
    if(topLevelCheck) return SubstIterator::getEmpty();
    splittable = false;
  }

  unifyFirstOrderStructure(t1,t2,splittable,sub);

  unsigned depth = env.options->higherOrderUnifDepth();

  if(!depth){
    return pvi(getSingletonIterator(sub));
  } else {
    return vi(new HigherOrderUnifiersIt(sub));    
  }
}

SubstIterator HOLUnification::postprocess(RobSubstitutionTL* sub)
{
  CALL("HOLUnification::postprocess");
   
  // We could carry out a fix point iteration here
  // but it is slighly involved and I am not sure that it is worth it.
  // will leave for now.

  unsigned depth = env.options->higherOrderUnifDepth();
  
  if(!depth || sub->emptyConstraints()){
    // if depth == 0, then we are unifying via dedicated inferences
    // if there are no constraints, then first-order unification sufficed
    return pvi(getSingletonIterator(sub));
  } else {
    return vi(new HigherOrderUnifiersIt(sub));    
  }
}

bool HOLUnification::associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::associate");

  TermList query(specialVar, /* special */ true);
  return unifyFirstOrderStructure(query, node, splittable, sub);
}


// TODO consider adding a check for loose De Bruijn indices
// see E prover code by Petar /TERMS/cte_fixpoint_unif.c
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
bool HOLUnification::unifyFirstOrderStructure(TermList t1, TermList t2, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::unifyFirstOrderStructure");

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

    TermList t1head = sub->derefBound(t1.head());
    TermList t2head = sub->derefBound(t2.head());

    ASS(!splittable || !t2.isVar())

    bool t2NotSplittable = !splittable && 
      (SortHelper::getResultSort(t2.term()).isArrowSort() || 
       SortHelper::getResultSort(t2.term()).isOrdinaryVar() ||
       t2head.isVar() ||
       t2head.isLambdaTerm());

    // Node term and query term must have the same type. Hence we do not
    // check type of query. We can rely on the t2NotSplittable check 
    if(!t1.isVar() && (t1head.isVar() || t1head.isLambdaTerm() || t2NotSplittable)) {
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