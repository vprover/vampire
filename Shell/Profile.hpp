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
 * @file Shell/Profile.hpp (syntactic properties of problems)
 *
 * @since 15/06/2008 Kemerovo
 */


#ifndef __Profile__
#define __Profile__

#include "Kernel/Unit.hpp"
#include "Lib/Array.hpp"

namespace Kernel
{
  class Clause;
  class Literal;
  class Term;
  class TermList;
}

using namespace std;
using namespace Kernel;
using namespace Lib;

#define HOW_MANY 10

namespace Shell {

/**
 * Represents syntactic properties of problems.
 */
class Profile 
{
 public:
  // constructor
  Profile();
  ~Profile();

  void scan(const UnitList*);
  vstring toString() const;
  bool lessThan(const Clause*,const Clause*);
  bool lessThan(const Literal*,const Literal*);

 private:
  void scan(const Clause*);
  void scan(const Literal*);
  void rescan(const Literal*);
  void descan(const Literal*);
  void scan(const TermList*);
  void scan(const Term*);
  int evaluate(const Clause* c);

  void output(const Clause* clause,ostream& str);
  void output(const Literal* clause,ostream& str,char pred);
  void output(const TermList* clause,ostream& str);
  void output(const Term* clause,ostream& str);


  /** The total number of clauses */
  unsigned _numberOfClauses;
  /** The number of different variables in this clause */
  unsigned _varsInThisClause;
  /** The number of different symbols in this clause */
  unsigned _symsInThisClause;
  /** currently processed clause */
  const Clause* _currentClause;
  /** _vars[i] stores the number of clauses with i variables */
  int _vars[HOW_MANY];
  /** _syms[i] stores the number of clauses with i symbols */
  int _syms[HOW_MANY];
  /** _lits[i] stores the number of clauses with i literals */
  int _lits[HOW_MANY];
  /** Array storing the number of occurrences of functions */
  int* _funs;
  /** Array storing the number of positive occurrences of predicates */
  int* _posPreds;
  /** Array storing the number of negative occurrences of predicates */
  int* _negPreds;
  /** Array storing the clauses in which a function occurs */
  const Clause** _funClauses;
  /** Array storing the clauses in which a predicate occurs */
  const Clause** _predClauses;

  /** Structure for counting the number of different variables in
   *  a clause.
   */
  class VarCounter
    : public Array<const Clause*>
  {
  public:
    VarCounter();
    void fillInterval(size_t start,size_t end);
  }; // class VarCounter

  VarCounter vc;
}; // class Profile

}

#endif // __Profile__
