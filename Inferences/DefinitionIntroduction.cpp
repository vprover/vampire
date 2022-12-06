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

namespace Inferences
{

Term *DefinitionIntroduction::lgg(Term *left, Term *right) {
  CALL("DefinitionIntroduction::lgg")

  unsigned fresh = 0;
  _substitution.reset();

  _function_scratch.push({left->functor(), left->arity(), left->arity()});
  SubtermIterator left_it(left);
  SubtermIterator right_it(right);
  while(left_it.hasNext()) {
    ALWAYS(right_it.hasNext());

    TermList left_top = left_it.next();
    TermList right_top = right_it.next();
    if(left_top.isTerm() && right_top.isTerm() && left_top.term()->functor() == right_top.term()->functor()) {
      unsigned functor = left_top.term()->functor();
      unsigned arity = left_top.term()->arity();
      _function_scratch.push({functor, arity, arity});
    }
    else {
      unsigned mapped;
      if(!_substitution.find({left_top, right_top}, mapped))
        _substitution.insert({left_top, right_top}, mapped = fresh++);

      _arg_scratch.push(TermList(mapped, false));
      left_it.right();
      right_it.right();
      _function_scratch.top().remaining--;
    }

    while(!_function_scratch.top().remaining) {
      IncompleteFunction record = _function_scratch.pop();
      Term *term = Term::create(record.functor, record.arity, _arg_scratch.end() - record.arity);
      _arg_scratch.truncate(_arg_scratch.length() - record.arity);
      _arg_scratch.push(TermList(term));

      if(_function_scratch.isNonEmpty())
        _function_scratch.top().remaining--;
      else
        break;
    }
  }

  ASS_EQ(_arg_scratch.length(), 1);
  return _arg_scratch.pop().term();
}

void DefinitionIntroduction::introduceDefinitionFor(Term *t) {
  CALL("DefinitionIntroduction::introduceDefinitionFor");

  if(!_defined.insert(t))
    return;

  TermList range_sort = SortHelper::getResultSort(t);

  DHMap<unsigned, TermList> sorts;
  SortHelper::collectVariableSorts(t, sorts);
  unsigned arity = sorts.size();

  Stack<TermList> domain_sorts;
  Stack<TermList> variables;
  for(unsigned i = 0; i < arity; i++) {
    domain_sorts.push(TermList(sorts.get(i)));
    variables.push(TermList(i, false));
  }

  unsigned functor = env.signature->addFreshFunction(arity, "sF");
  OperatorType *type = OperatorType::getFunctionType(arity, domain_sorts.begin(), range_sort);
  env.signature->getFunction(functor)->setType(type);

  Term *def = Term::create(functor, arity, variables.begin());
  Literal *eq = Literal::createEquality(true, TermList(def), TermList(t), range_sort);

  NonspecificInference0 inference(UnitInputType::AXIOM, InferenceRule::FUNCTION_DEFINITION);
  Clause *definition = new (1) Clause(1, inference);
  (*definition)[0] = eq;

  _definitions.push(definition);
}

void DefinitionIntroduction::process(Term *t) {
  CALL("DefinitionIntroduction::process(Term *)");

  unsigned functor = t->functor();
  Stack<Entry> &entries = _entries[functor];

  unsigned i = 0;
  for(i = 0; i < entries.length(); i++) {
    Entry &entry = entries[i];
    Term *gen = lgg(entry.term, t);
    if(gen->allArgumentsAreVariables() && gen->getDistinctVars() == gen->arity())
      continue;

    entry.term = gen;
    if(++entry.count > env.options->functionDefinitionIntroduction()) {
      introduceDefinitionFor(entry.term);
      std::swap(entries[i], entries.top());
      entries.pop();
      return;
    }
  }

  if(i == entries.length())
    entries.push({t, 1});
}

void DefinitionIntroduction::process(Clause *cl) {
  CALL("DefinitionIntroduction::process(Clause *)");

  if(cl->inference().rule() == InferenceRule::FUNCTION_DEFINITION)
    return;

  while(_entries.length() < env.signature->functions())
    _entries.push(Stack<Entry>());

  for(unsigned i = 0; i < cl->length(); i++) {
    NonVariableNonTypeIterator it((*cl)[i]);
    while(it.hasNext()) {
      TermList next = it.next();
      Term *t = next.term();
      if(t->allArgumentsAreVariables() && t->getDistinctVars() == t->arity())
        continue;

      process(t);
    }
  }
}

ClauseIterator DefinitionIntroduction::generateClauses(Clause *cl) {
  CALL("DefinitionIntroduction::generateClauses");

  _definitions.reset();
  process(cl);
  return pvi(decltype(_definitions)::Iterator(_definitions));
}

}
