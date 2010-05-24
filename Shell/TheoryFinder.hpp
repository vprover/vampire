/**
 * @file TheoryFinder.hpp
 * Defines methods for finding theories in the input problems.
 *
 * @since 09/06/2004 Manchester
 * @since 09/07/2008 Linz, changed to new datastructures
 */

#ifndef __TheoryFinder__
#define __TheoryFinder__

#include "Kernel/Unit.hpp"

namespace Kernel {
  class Clause;
  class Formula;
  class Literal;
}

using namespace Kernel;

namespace Shell {

class Property;

/**
 * This class defines methods for finding known theories in the input problem.
 * @since 09/06/2004 Manchester
 */
class TheoryFinder {
public:
  TheoryFinder(const UnitList*,Property* property);
  ~TheoryFinder();
  int search();

private:
  bool matchAll(const Unit* unit);
  bool matchAll(const Clause* clause);
  bool matchAll(const Formula* formula);
  bool matchAll(const Literal* literal);
  bool matchCode(const void* obj,const unsigned char* code,int prop);

//   bool match(const unsigned char* code,const Formula* formula); 
//   bool match(const unsigned char* code,const Clause* clause); 
//   bool match(const unsigned char* code,const Literal* lit); 

//   bool matchCode(const Formula* f,const unsigned char* code,
// 		 const char* name,int arity,int prop);
  bool matchC(const Literal*);
  bool matchA(const Literal*);
  bool matchLeftInverse(const Literal*);
  bool matchLeftIdentity(const Literal*);
  bool matchRightInverse(const Literal*);
  bool matchRightIdentity(const Literal*);
  bool matchLeftDistributivity(const Literal*);
  bool matchRightDistributivity(const Literal*);
  bool matchRobbins(const Literal*);
  bool matchIdempotence(const Literal*);
  bool matchAssociator(const Literal*);
  bool matchCommutator(const Literal*);
  bool matchAlternative(const Literal*);
  bool matchAbsorption(const Literal*);
  bool matchCombinatorS(const Literal*);
  bool matchCombinatorB(const Literal*);
  bool matchCombinatorT(const Literal*);
  bool matchCombinatorO(const Literal*);
  bool matchCombinatorQ(const Literal*);

  bool matchExtensionality(const Formula*);
  bool matchExtensionality(const Clause*);
  bool matchCondensedDetachment1(const Clause*);
  bool matchCondensedDetachment2(const Clause*);
  bool matchFLD1(const Clause*);
  bool matchFLD2(const Clause*);
  bool matchSubset(const Formula*);
  bool matchSubset(const Clause*);

// //    void assert(const char* name,
// //  	      int arity,
// //  	      const Symbol** theorySymbols,
// // 	      Unit* result);
//   void analyse(const Clause*);

  /**
   * Codes of various symbols.
   * @since 23/06/2004 Dresden.
   */
  enum Code {
    /** new variable, followed by its number in the array of variables */
    NEWVAR = 1,
    /** old variable, followed by its number in the array of variables */
    OLDVAR = 2,
    /** new function symbol, followed by its arity and number in the array of symbols */
    NEWFUN = 3,
    /** old function symbol, followed by its number in the array of symbols */
    OLDFUN = 4,
    /** conjunction, followed by its length */
    CAND = 5,
    /** disjunction, followed by its length */
    COR = 6,
    /** implication */
    CIMP = 7,
    /** negation */
    CNOT = 8,
    /** equivalence */
    CIFF = 9,
    /** xor */
    CXOR = 10,
    /** universal quantifier, followed by its length and variable numbers */
    CFORALL = 11,
    /** existential quantifier, followed by its length and variable numbers */
    CEXISTS = 12,
    /** equality symbol */
    EQL = 13,
    /** positive literal in a formula */
    POS = 14,
    /** negative literal in a formula */
    NEG = 15,
    /** term in a list, followed by its number */
    TERM = 16,
    /** formula in a list, followed by its number */
    FORM = 17,
    /** new function symbol, followed by its arity and number
     * in the array of symbols, the next argument in the list is not saved */
    NEWFUN1 = 18,
    /** old function symbol, followed by its number in the array of symbols,
     *  the next argument in the list is not saved */
    OLDFUN1 = 19,
    /** old variable, followed by its number in the array of variables,
     * the next argument in the list is not saved */
    OLDVAR1 = 20,
    /** positive literal in a list, followed by its number */
    PLIT = 21,
    /** negative literal in a list, followed by its number */
    NLIT = 22,
    /** clause */
    CLS = 23,
    /** new predicate symbol, followed by its arity and number in the array of symbols */
    NEWPRED = 24,
    /** old predicate symbol, followed by its number in the array of symbols */
    OLDPRED = 25,
    /** conjunction, followed by its length */
    /** end of code */
    END = 0
  };

  class Backtrack;

  /** The problem itself */
  const UnitList* _units;
  /** property to be filled with some information about found theories,
      may be null */
  Property* _property;  
};

}

#endif
