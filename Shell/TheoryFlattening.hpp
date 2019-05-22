
/*
 * File TheoryFlattening.hpp.
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
  TheoryFlattening() : _recursive(true), _sharing(false), _grouping(true) {}

  /** Initializes the flattener with the following options:
       rec: if false, only the children of top level functions are flatten.
            if true, also subterms are flattened.
       share: if true, shared subterms will be assigned the same variable
       grouping: if true, new variables are introduced when the function is a
                 theory (nontheory) clause and the argument is a nontheory
                 (theory) node.
                 if false, arguments are always flattened
   */
  TheoryFlattening(bool rec, bool share, bool grouping);
  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(ClauseList*& units);
  Clause* apply(Clause*& cl,Stack<Literal*>& target);
  Clause* apply(Clause*& cl){
    static Stack<Literal*> dummy;
    return apply(cl,dummy);
  }
  bool apply(Stack<Literal*>& lits,Stack<Literal*>& result, unsigned maxVar);
private:
  Literal* replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar,
                           DHMap<Term*,unsigned>& abstracted);
  Term* replaceTopTermsInTerm(Term* term, Stack<Literal*>& newLits,
                              unsigned& maxVar,bool interpreted,
                              DHMap<Term*,unsigned>& abstracted);

  bool _recursive;
  bool _sharing;
  bool _grouping;
};

};

#endif /* __TheoryFlattening__ */
