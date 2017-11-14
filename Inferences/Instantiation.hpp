
/*
 * File Instantiation.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
#include "Kernel/Sorts.hpp"

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
  VirtualIterator<Term*> getCandidateTerms(Clause* cl, unsigned var,unsigned sort);
  class AllSubstitutionsIterator;
  struct ResultFn;

  void tryMakeLiteralFalse(Literal*, Stack<Substitution>& subs);
  Term* tryGetDifferentValue(Term* t); 

  DHMap<unsigned,Lib::Set<Term*>*> sorted_candidates_check;
  DHMap<unsigned,Lib::Stack<Term*>*> sorted_candidates;

};

};

#endif /*__Instantiation__*/
