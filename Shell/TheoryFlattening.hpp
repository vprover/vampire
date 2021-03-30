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
 * @file TheoryFlattening.hpp
 * Defines class TheoryFlattening.
 */


#ifndef __TheoryFlattening__
#define __TheoryFlattening__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Kernel/Term.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class for flattening clauses to separate theory and non-theory parts
 */
class TheoryFlattening
{
public:
  TheoryFlattening() : _recursive(true), _sharing(false) {}
  TheoryFlattening(bool rec, bool share); 
  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(ClauseList*& units);
  Clause* apply(Clause*& cl,Stack<Literal*>& target);
  Clause* apply(Clause*& cl){
    static Stack<Literal*> dummy;
    return apply(cl,dummy);
  }
private:
  Literal* replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar,
                           DHMap<Term*,unsigned>& abstracted);
  Term* replaceTopTermsInTerm(Term* term, Stack<Literal*>& newLits,
                              unsigned& maxVar,bool interpreted,
                              DHMap<Term*,unsigned>& abstracted);

  bool _recursive;
  bool _sharing;
};

};

#endif /* __TheoryFlattening__ */
