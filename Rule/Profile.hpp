/**
 * @file Profile.hpp (syntactic properties of problems)
 *
 * @since 15/06/2008 Kemerovo
 */


#ifndef __Profile__
#define __Profile__

#include "../Kernel/Unit.hpp"
#include "../Lib/Array.hpp"

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

/**
 * Namespace for the rule-based inference engine.
 * @since 12/07/2008 Linz
 */
namespace Rule {

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
  string toString() const;
  bool lessThan(const Clause*,const Clause*);
  bool lessThan(const Literal*,const Literal*);
  unsigned numberOfPositiveOccurrences(unsigned predicate);
  unsigned numberOfNongroundArguments(unsigned predicate,
				      unsigned argNumber,
				      bool polarity);

  /**
   * Class representing profile of predicates.
   * @since 02/07/2008 train London-Manchester
   */
  class Predicate
  {
  public:
    /** Number of occurrences */
    unsigned occurrences;
    /** replacement for a constructor */
    void initialise(unsigned arity)
    {
      occurrences = 0;
      if (arity > 0) {
	argCounter = (unsigned*)ALLOC_KNOWN(2*sizeof(unsigned)*arity,
					    "Profile::groundCounter");
      }
      for (int i = arity*2-1;i >= 0;i--) {
	argCounter[i] = 0;
      }
    }
    /** replacement for a destructor */
    void destroy(unsigned arity)
    {
      if (arity > 0) {
	DEALLOC_KNOWN(argCounter,
		      2*sizeof(unsigned)*arity,
		      "Profile::groundCounter");
      }
    }
    /** counters of non-ground occurrences of arguments */
    unsigned* argCounter;
    /** add n to the argument counter */
    void incrementArgumentCounter(unsigned arg,bool polarity,int increment)
    {
      argCounter[2*arg + (polarity ? 1 : 0)] += increment;
    }
    /** get the value of the argument counter */
    unsigned getArgumentCounter(unsigned arg,bool polarity)
    {
      return argCounter[2*arg + (polarity ? 1 : 0)];
    }
  };

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
  /** Array storing the clauses in which a function occurs */
  const Clause** _funClauses;
  /** Array storing the clauses in which a predicate occurs */
  const Clause** _predClauses;
  /** The number of predicates at the moment Profile was created */
  unsigned _numberOfHeaders;
  /** The number of functions at the moment Profile was created */
  unsigned _numberOfFunctions;

  Predicate* _predicates;

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
