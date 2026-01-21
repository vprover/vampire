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
 * @file DefinitionIntroduction.cpp
 */

#include "DefinitionIntroduction.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Lib/Metaiterators.hpp"

struct IncompleteFunction {
  unsigned functor, arity, remaining;
  bool typeCon;
};

// compute the least general generalisation of `left` and `right`
static Term *lgg(Term *left, Term *right) {
  ASS_EQ(left->functor(), right->functor())
  if(left == right)
    return left;

  // arguments to be used when creating the generalisation term
  std::vector<TermList> args;
  // remaining parts of the term that should be created
  std::vector<IncompleteFunction> skeleton;
  // map from left-right pairs of subterms to their variables
  DHMap<std::pair<TermList, TermList>, unsigned> substitution;

  // fresh variable where necessary
  unsigned fresh = 0;

  // iterate through left and right subterms at the same time
  SubtermIterator left_subterms(left);
  SubtermIterator right_subterms(right);
  while(left_subterms.hasNext()) {
    ALWAYS(right_subterms.hasNext());
    TermList left = left_subterms.next();
    TermList right = right_subterms.next();
    // if we have f(...) ~ f(...), descend into subterms
    if(left.isTerm() && right.isTerm() && left.term()->functor() == right.term()->functor()) {
      Term *leftt = left.term();
      unsigned functor = leftt->functor();
      unsigned arity = leftt->arity();
      unsigned remaining = arity;
      bool typeCon = leftt->isSort();
      // put something in the skeleton to finish later
      skeleton.push_back({functor, arity, remaining, typeCon});
    }
    else {
      // make or retrieve a new variable to represent the pair
      // variable/variable is a bit of a weird case, but it works out
      unsigned mapped;
      if(!substitution.find({left, right}, mapped))
        substitution.insert({left, right}, mapped = fresh++);

      args.emplace_back(mapped, false);
      // skip subterms below a disagreement
      left_subterms.right();
      right_subterms.right();

      // we just finished a term
      if(!skeleton.empty())
        skeleton.back().remaining--;
    }

    // did something, check if we can put some meat back on the skeleton
    while(!skeleton.empty() && !skeleton.back().remaining) {
      // finish the last term using `args`
      IncompleteFunction record = skeleton.back();
      skeleton.pop_back();
      size_t before = args.size() - record.arity;
      Term *term = record.typeCon
        ? AtomicSort::create(record.functor, record.arity, args.data() + before)
        : Term::create(record.functor, record.arity, args.data() + before);
      args.resize(before);
      args.emplace_back(term);

      if(!skeleton.empty())
        skeleton.back().remaining--;
      else
        break;
    }
  }

  ASS_EQ(args.size(), left->arity());
  return Term::create(left->functor(), left->arity(), args.data());
}

namespace Inferences
{
void DefinitionIntroduction::introduceDefinitionFor(Term *t) {
  // check not already inserted
  if(auto [_, inserted] = _defined.insert(t); !inserted)
    return;

  // compute domain and range sorts
  DHMap<unsigned, TermList> domain_sorts;
  TermList range_sort = SortHelper::getResultSort(t);
  SortHelper::collectVariableSorts(t, domain_sorts);

  // reformat data
  std::vector<TermList> domain_sort_vector;
  std::vector<TermList> variables;
  unsigned term_arity = 0, sort_arity = 0;

  // OperatorType expects a canonically-renamed type
  Renaming sort_rename;

  // first, sort variables
  for(auto [x, sort] : iterTraits(domain_sorts.items()))
    if(sort == AtomicSort::superSort()) {
      sort_arity++;
      variables.emplace_back(x, false);
      sort_rename.getOrBind(x);
    }
  // ...now term variables
  for(auto [x, sort] : iterTraits(domain_sorts.items()))
    if(sort != AtomicSort::superSort()) {
      term_arity++;
      variables.emplace_back(x, false);
      domain_sort_vector.push_back(sort_rename.apply(sort));
    }

  // create the equation
  unsigned functor = env.signature->addFreshFunction(term_arity + sort_arity, "sF");
  OperatorType *type = OperatorType::getFunctionType(
    term_arity,
    domain_sort_vector.data(),
    sort_rename.apply(range_sort),
    sort_arity
  );
  env.signature->getFunction(functor)->setType(type);
  Term *def = Term::create(functor, sort_arity + term_arity, variables.data());
  Literal *eq = Literal::createEquality(true, TermList(def), TermList(t), range_sort);

  // record definition
  auto definition = Clause::fromLiterals({eq}, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::FUNCTION_DEFINITION));
  InferenceStore::instance()->recordIntroducedSymbol(definition, SymbolType::FUNC, functor);
  _definitions.push_back(definition);
}

void DefinitionIntroduction::process(Term *t) {
  std::vector<Entry> &entries = _entries[t->functor()];
  for(Entry &entry : entries) {
    // find the first entry for `t` with a non-trivial lgg
    Term *gen = lgg(entry.term, t);
    if(gen->allArgumentsAreVariables() && gen->getDistinctVars() == gen->arity())
      continue;

    // bump that entry's weight
    entry.term = gen;
    entry.weight += t->weight();
    // when over threshold, introduce the definition
    if(entry.weight > env.options->functionDefinitionIntroduction()) {
      introduceDefinitionFor(entry.term);
      std::swap(entry, entries.back());
      entries.pop_back();
    }

    // in either case, done here
    return;
  }

  // if none found, insert `t` by itself
  entries.push_back({t, t->weight()});
}

void DefinitionIntroduction::process(Clause *cl) {
  // don't process our own clauses
  if(cl->inference().rule() == InferenceRule::FUNCTION_DEFINITION)
    return;

  // this can happen with e.g. induction or CNFOnTheFly introducing new symbols
  while(_entries.size() < env.signature->functions())
    _entries.emplace_back();

  // process all the non-trivial terms in the clause
  for(Literal *l : cl->iterLits())
    for(Term *t : iterTraits(NonVariableNonTypeIterator(l)))
      if(!t->allArgumentsAreVariables() || t->getDistinctVars() < t->arity())
        process(t);
}

}
