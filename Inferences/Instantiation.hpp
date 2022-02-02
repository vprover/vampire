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
 * @file Instantiation.hpp
 * Defines class Instantiation
 * @author Giles
 */

#ifndef __Instantiation__
#define __Instantiation__

#include "Forwards.hpp"
#include "Lib/Set.hpp"
#include "Kernel/OperatorType.hpp"

#include "Kernel/Theory.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;


class Instantiation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Instantiation);
  USE_ALLOCATOR(Instantiation);

  Instantiation() {}

  //void init();

  ClauseIterator generateClauses(Clause* premise);

  void registerClause(Clause* cl);

private:
  VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,TermList sort);
  class AllSubstitutionsIterator;
  struct ResultFn;

  void tryMakeLiteralFalse(Literal*, Stack<Substitution>& subs);
  Term* tryGetDifferentValue(Term* t); 

  DHMap<TermList,Lib::Set<Term*>*> sorted_candidates_check;
  DHMap<TermList,Lib::Stack<Term*>*> sorted_candidates;

};

};

#endif /*__Instantiation__*/