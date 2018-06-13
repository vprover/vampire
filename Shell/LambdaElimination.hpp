/**
 * @file LambdaElimination.hpp
 * Defines class LambdaElimination.
 */

#ifndef __LambdaElimination__
#define __LambdaElimination__

#include "Lib/Deque.hpp"
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

  //defines the mamximum order of the sort for any combinator
  //added during heuristic combinator addition. Only utilised
  //if the by_rank option set
  static const unsigned MAX_ORDER = 4;
  static const unsigned MAX_SORTS = 15;
  static const unsigned MULT_FACTOR = 2;

  LambdaElimination() : _axioms(0), _combinatorAdditionMode(true){};
  LambdaElimination(DHMap<unsigned,unsigned> varSorts) : _axioms(0), _varSorts(varSorts), _combinatorAdditionMode(false){};
  TermList elimLambda(Term* lambdaTerm);

  /** Iterates through sorts in problem and heuristically adds
    * a set of relevanr combinators to the problem along with their defining
    * equations.
    */  
  void addCombinatorsHeuristically(UnitList*& units);
  
  static unsigned introduceAppSymbol(unsigned sort1, unsigned sort2, unsigned resultSort); 
  static void buildFuncApp(unsigned function, TermList args1, TermList arg2, TermList& functionApplication);

  void inline addAxiomsToUnits(UnitList*& units){
    if(_axioms){
      units = UnitList::concat(_axioms, units);
    }
    _axioms = 0;
  }
  
  UnitList* axioms(){
	 return _axioms;
  }

private:
 
  typedef Stack<unsigned> SortStack; 
  bool tryAddCombinatorFromSort(unsigned sort, Deque<unsigned>& sortQ);
  bool isSCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, unsigned sort3, unsigned &combSort);
  bool isBCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, SortStack &combSort);
  bool isCCompatible(unsigned combinedSort, unsigned sort1, unsigned sort2, unsigned sort3, unsigned &combSort);

  //keeps track of number of combinators added
  unsigned _combinatorsAdded;
  //maximum number of combinators that can be added
  unsigned _maxCombinatorsToBeAdded;
  
  unsigned countBasicSorts(Sorts::FunctionSort* fsort);
  
  /*********************************************
  * Lambda and application elimination functions
  *********************************************/
  
  UnitList* _axioms;
  
  unsigned sortOf(TermList t);

  
  void addToProcessed(TermList ts, 	Stack<unsigned> &_argNums);
  /** Add a new definitions to _defs */
  void addAxiom(FormulaUnit* axiom);

  void addQuantifierAxiom(TermList constant, unsigned constSort, Connective conn, unsigned qvarSort);
  void addNotConnAxiom(TermList constant, unsigned notsort);
  void addBinaryConnAxiom(TermList constant, Connective conn, unsigned connSort, unsigned appedOnce);
  void addEqualityAxiom(TermList equals, unsigned argsSort, unsigned eqaulsSorts);
  
  void addCombinatorAxiom(TermList combinator, unsigned combinatorSort, unsigned argSort,
                          Signature::Symbol::HOLConstant comb, int arg1Sort = -1, int arg2Sort = -1);
  // Introduces a fresh predicate or function (depending on the context) symbol
  // with given arguments and result sort

  void dealWithApp(TermList lhs, TermList rhs, unsigned sort, int lambdaVar, Stack<TermList> &_toBeProcessed, Stack<unsigned> &_argNums);
  
  unsigned range(unsigned sort);
  unsigned domain(unsigned sort);
  
  Formula* createEquality(TermList t1, TermList t2, unsigned sort);
  Formula* toEquality(TermList booleanTerm);
  
  TermList processBeyondLambda(Term* term);
  TermList addKComb(unsigned appliedToArg, TermList arg);
  TermList addComb(unsigned appliedToArgs, TermList arg1, TermList arg2, Signature::Symbol::HOLConstant comb);
  
  TermList addHolConstant(vstring name, unsigned sort, bool& added, Signature::Symbol::HOLConstant constant);
  void process(Stack<int> _vars, Stack<unsigned> _sorts, Stack<TermList> _toBeProcessed);
  
  /** Lexical scope of the current unit */
  DHMap<unsigned,unsigned> _varSorts;
  bool _combinatorAdditionMode;
  //Stack<int> _vars;
  //Stack<unsigned> _sorts;
  //Stack<unsigned> _argNums;
  //Stack<TermList> _toBeProcessed;
  Stack<TermList> _processed;
  Stack<Signature::Symbol::HOLConstant> _combinators;
  Stack<unsigned> _combSorts;
  
  TermList _processing; 

};

#endif // __LambdaElimination__
