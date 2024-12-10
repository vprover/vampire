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
 * @file PredicateTypePromotion.cpp
 * A preprocessing step which lifts unary predicates to sorts in some cases
 */

#include "PredicateTypePromotion.hpp"

#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include <vector>
#include <unordered_map>
#include <unordered_set>

using namespace Kernel;

static Literal *createLiteralEliminatingInjectivity(Literal *l, unsigned functor, TermList *args) {
  if(
    l->isEquality() &&
    args[0].isTerm() && args[0].term()->functor() == functor &&
    args[1].isTerm() && args[1].term()->functor() == functor
  )
    return Literal::createEquality(
      l->polarity(),
      args[0].term()->termArg(0),
      args[1].term()->termArg(0),
      SortHelper::getArgSort(args[0].term(), 0)
    );
  return Literal::create(l, args);
}

static Literal *injectVars(Literal *l, unsigned functor, const std::unordered_set<unsigned> &vars) {
  std::vector<TermList> args;
  for(unsigned i = 0; i < l->numTermArguments(); i++)
    args.push_back(BottomUpEvaluation<TermList, TermList>()
      .function([&](TermList t, TermList *evaluatedChildren) {
        if(!t.isVar())
          return TermList(Term::create(t.term(), evaluatedChildren));
        if(!vars.count(t.var()))
          return t;
        return TermList(Term::create(functor, 1, &t));
      })
      .apply(l->termArg(i))
    );
  return createLiteralEliminatingInjectivity(l, functor, args.data());
}

static Literal *mapConstants(Literal *l, unsigned functor, std::unordered_map<Term *, Term *> constants) {
  std::vector<TermList> args;
  for(unsigned i = 0; i < l->numTermArguments(); i++)
    args.push_back(BottomUpEvaluation<TermList, TermList>()
      .function([&](TermList t, TermList *evaluatedChildren) {
        if(t.isVar())
          return t;
        Term *tt = t.term();
        if(auto it = constants.find(tt); it != constants.end())
          return TermList(it->second);
        return TermList(Term::create(tt, evaluatedChildren));
      })
      .apply(l->termArg(i))
    );
  return createLiteralEliminatingInjectivity(l, functor, args.data());
}

namespace Shell {

void PredicateTypePromotion::apply(Kernel::Problem &prb) {
  // TODO what does polymorphism mean?
  if(prb.hasPolymorphicSym())
    return;

  std::unordered_set<unsigned> eliminated;
  while(true) {
    std::unordered_map<unsigned, bool> candidate_predicates;
    for(unsigned i = 0; i < env.signature->predicates(); i++)
      if(
        auto *p = env.signature->getPredicate(i);
        p->arity() == 1 && p->numTypeArguments() == 0 && p->usageCnt() && !eliminated.count(i)
      )
        candidate_predicates.insert({i, false});

    UnitList::Iterator scan_it(prb.units());
    while(scan_it.hasNext()) {
      Clause *cl = scan_it.next()->asClause();
      for(Literal *l : cl->iterLits()) {
        unsigned functor = l->functor();
        if(!candidate_predicates.count(functor))
          continue;
        TermList arg = l->termArg(0);
        if(( l->polarity() && (cl->length() != 1 || arg.isVar() || arg.term()->arity())) ||
           (!l->polarity() && arg.isTerm()))
          candidate_predicates.erase(functor);
        if(l->polarity() && cl->length() == 1 && arg.isTerm() && arg.term()->arity() == 0)
          candidate_predicates[functor] = true;
      }
    }
    for(auto it = candidate_predicates.cbegin(); it != candidate_predicates.cend();)
      if(!it->second)
        candidate_predicates.erase(it++);
      else
        ++it;

    if(candidate_predicates.empty())
      return;

    unsigned functor = candidate_predicates.begin()->first;
    Signature::Symbol *p = env.signature->getPredicate(functor);
    std::cout << "sort detected: " << p->name() << '\n';
    TermList base_sort = p->predType()->arg(0);

    bool added;
    unsigned new_sort_functor = env.signature->addTypeCon("sS" + p->name(), 0, added);
    ASS(added)
    TermList new_sort(AtomicSort::createConstant(new_sort_functor));
    OperatorType *new_sort_to_base_sort = OperatorType::getFunctionType(1, &new_sort, base_sort);
    unsigned injection = env.signature->addFunction("sG" + p->name() + "_inj", 1);
    env.signature->getFunction(injection)->setType(new_sort_to_base_sort);
    ASS(added)
    // TODO prb.addEliminatedPredicate(functor, ???);

    std::unordered_map<Term *, Term *> constants;
    UnitList::DelIterator delete_it(prb.units());
    while(delete_it.hasNext()) {
      Clause *cl = delete_it.next()->asClause();
      if(cl->length() == 1 && (*cl)[0]->functor() == functor && (*cl)[0]->polarity()) {
        Literal *l = (*cl)[0];
        TermList arg = l->termArg(0);
        if(l->polarity() && !constants.count(arg.term())) {
          Term *c = arg.term();
          unsigned new_c_functor = env.signature->addFunction("sG" + c->functionName(), 0);
          env.signature->getFunction(new_c_functor)->setType(OperatorType::getConstantsType(new_sort));
          TermList new_c(Term::createConstant(new_c_functor));
          constants.insert({c, Term::create(injection, 1, &new_c)});
        }
        delete_it.del();
        continue;
      }

      if(!cl->iterLits().any([functor](Literal *l) { return l->functor() == functor; }))
        continue;

      std::vector<Literal *> lits;
      std::unordered_set<unsigned> replace_vars;
      for(Literal *l : cl->iterLits()) {
        if(l->functor() == functor)
          replace_vars.insert(l->termArg(0).var());
        else
          lits.push_back(l);
      }
      for(Literal *&l : lits)
        l = injectVars(l, injection, replace_vars);

      // TODO proper inference
      cl = Clause::fromArray(lits.data(), lits.size(), FromInput(UnitInputType::AXIOM));
      delete_it.insert(cl);
      delete_it.del();
    }

    UnitList::RefIterator replace_it(prb.units());
    while(replace_it.hasNext()) {
      Unit *&u = replace_it.next();
      Clause *cl = u->asClause();
      bool changed = false;
      std::vector<Literal *> lits;
      for(Literal *l : cl->iterLits()) {
        Literal *replaced = mapConstants(l, injection, constants);
        changed = changed || l != replaced;
        lits.push_back(replaced);
      }
      if(changed)
        // TODO proper inference
        u = Clause::fromArray(lits.data(), lits.size(), FromInput(UnitInputType::AXIOM));
    }

    if(prb.hasEquality()) {
      TermList x(0, false), y(1, false);
      std::vector<Literal *> lits = {
        Literal::createEquality(true, x, y, new_sort),
        Literal::createEquality(false,
          TermList(Term::create(injection, 1, &x)),
          TermList(Term::create(injection, 1, &y)),
          base_sort
        ),
      };
      // TODO proper inference
      Clause *cl = Clause::fromArray(lits.data(), lits.size(), FromInput(UnitInputType::AXIOM));
      UnitList::push(cl, prb.units());
    }

    eliminated.insert(functor);
  }
  prb.invalidateEverything();
}

}
