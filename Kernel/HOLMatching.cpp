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

#include "Kernel/HOLMatching.hpp"
#include "Kernel/ApplicativeHelper.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

bool HOLInstantiation::match(TermList base, TermList instance, RobSubstitutionTL* sub)
{
  CALL("HOLInstantiation::match");

#define DEBUG_MATCH(lvl, ...) if (lvl < 2) DBG("match: ", __VA_ARGS__)
  if(sub->sameTermContent(base,instance)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  sub->bdRecord(localBD);

  static Stack<Constraint> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(Constraint(base, instance));

  // add encountered store??

  // Iteratively resolve matching pairs in toDo
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermList bt = x.lhs();
    TermList it = x.rhs();
    DEBUG_MATCH(1, "next pair: ", tie(bt, it))

    if(bt.isSpecialVar()) {
      auto binding = sub->_bank.find(bt);
      if(binding) {
        bt = binding.unwrap();
        toDo.push(Constraint(bt,it));
        continue;
      } else {
        sub->bind(bt, it);
      }  
    } else if(it.isSpecialVar()) {
      auto binding = sub->_bank.find(it);
      if(binding) {
        it = binding.unwrap();
        toDo.push(Constraint(bt,it));
        continue;
      } else {
        sub->bind(it, bt);
      }  
    } else {
      ApplicativeHelper::normaliseLambdaPrefixes(bt,it);

      if (bt.isVar()){
        auto binding = sub->_bank.find(bt);
        
        if(binding) {
          auto b = binding.unwrap();
          if(!TermList::equals(b, it))
          {
            mismatch=true;
            break;
          }
        } else {
          if(it.containsLooseIndex()){
            mismatch = true;
            break;
          }
          sub->bind(bt, it);
        }
      } else if (it.isVar()) {
        mismatch=true;
        break;      
      } else if (bt.term()->functor() == it.term()->functor()) {
        for (unsigned i = 0; i < bt.term()->arity(); i++) {
          toDo.push(Constraint(bt.nthArg(i), it.nthArg(i)));
        }
      } else {
        mismatch = true;  
        break;
      }
    }

    ASS(!mismatch)
  }

  if(mismatch) {
    toDo.reset();
  }

  sub->bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(sub->bdIsRecording()) {
      sub->bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}

bool HOLInstantiation::associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLInstantiation::associate");

  TermList query(specialVar, /* special */ true);
  return match(query, node, sub);  
}

bool HOLGeneralisation::associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub)
{
  CALL("HOLGeneralisation::associate");

  TermList query(specialVar, /* special */ true);
  return HOLInstantiation::match(node, query, sub);  
}

}

}

#endif