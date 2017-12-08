/**
 * @file LambdaElimination.hpp
 * Defines class LambdaElimination.
 */

#ifndef __LambdaElimination__
#define __LambdaElimination__

#include "Forwards.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * A class with function @b elimLambda() that eliminates a lambda expressions
 * It does this by applying the well known rewrite rules for SKIBC combinators.
 *
 * These can be found:
 * https://en.wikipedia.org/wiki/Combinatory_logic
 */
class LambdaElimination {
public:

  LambdaElimination(DHMap<unsigned,unsigned> varSorts) : _axioms(0), _varSorts(varSorts){};
  TermList elimLambda(Term* lambdaTerm);
  
  static unsigned introduceAppSymbol(unsigned sort1, unsigned sort2, unsigned resultSort); 
  static void buildFuncApp(unsigned function, TermList args1, TermList arg2, TermList& functionApplication);
  
  UnitList* axioms(){
	 return _axioms;
  }

private:
  /*********************************************
  * Lambda and application elimination functions
  *********************************************/
  
  UnitList* _axioms;
  
  unsigned sortOf(TermList t);

  
  void addToProcessed(TermList ts);
  /** Add a new definitions to _defs */
  void addAxiom(FormulaUnit* axiom);

  void addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned qvarSort);
  void addNotConnAxiom(TermList constant, unsigned notsort);
  void addBinaryConnAxiom(TermList constant, Connective conn, unsigned connSort, unsigned appedOnce);
  void addEqualityAxiom(TermList equals, unsigned argsSort, unsigned eqaulsSorts);
  
  void addCombinatorAxiom(TermList combinator, unsigned combinatorSort, unsigned argSort,
                          Term::Comb comb, int arg1Sort = -1, int arg2Sort = -1);
  // Introduces a fresh predicate or function (depending on the context) symbol
  // with given arguments and result sort

  void dealWithApp(TermList lhs, TermList rhs, unsigned sort, int lambdaVar);
  
  unsigned range(unsigned sort);
  unsigned domain(unsigned sort);
  
  Formula* createEquality(TermList t1, TermList t2);
  Formula* toEquality(TermList booleanTerm);
  
  TermList processBeyondLambda(Term* term);
  TermList addKComb(unsigned appliedToArg, TermList arg);
  TermList addComb(unsigned appliedToArgs, TermList arg1, TermList arg2, Term::Comb comb);
  
  TermList addHolConstant(vstring name, unsigned sort, bool& added, Term::Comb combType);
  void process();
  
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;
  
  Stack<int> _vars;
  Stack<unsigned> _sorts;
  Stack<unsigned> _argNums;
  Stack<TermList> _toBeProcessed;
  Stack<TermList> _processed;
  Stack<Term::Comb> _combinators;
  Stack<unsigned> _combSorts;
  
  TermList _processing; 

};

#endif // __LambdaElimination__
