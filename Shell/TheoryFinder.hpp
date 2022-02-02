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
 *
 * TODO 25/03/2021 update class to handle polymorphism. Polymorphism changes the form
 * of the various axioms, so the codes need updating.
 */
class TheoryFinder {
public:
  TheoryFinder(const UnitList*,Property* property);
  ~TheoryFinder();
  int search();
  static bool matchCode(const void* obj,const unsigned char* code);
  static bool matchKnownExtensionality(const Clause*);

private:
  bool matchAll(const Unit* unit);
  bool matchAll(const Clause* clause);
  bool matchAll(const Formula* formula);
  bool matchAll(const Literal* literal);
  bool matchCode(const void* obj,const unsigned char* code,uint64_t prop);

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
  bool matchListConstructors(const Formula*);
  bool matchTest(const Formula*);

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
    NEWVAR,
    /** old variable, followed by its number in the array of variables */
    OLDVAR,
    /** new function symbol, followed by its arity and number in the array of symbols */
    NEWFUN,
    /** old function symbol, followed by its number in the array of symbols */
    OLDFUN,
    /** conjunction, followed by its length */
    CAND,
    /** disjunction, followed by its length */
    COR,
    /** implication */
    CIMP,
    /** negation */
    CNOT,
    /** equivalence */
    CIFF,
    /** non-backtrackable equivalence */
    NBCIFF,
    /** xor */
    CXOR,
    /** universal quantifier, followed by its length and variable numbers */
    CFORALL,
    /** existential quantifier, followed by its length and variable numbers */
    CEXISTS,
    /** equality symbol */
    EQL,
    /** positive literal in a formula */
    POS,
    /** negative literal in a formula */
    NEG,
    /** term in a list, followed by its number */
    TERM,
    /** formula in a list, followed by its number */
    FORM,
    /** A new function symbol, followed by its arity and number
     * in the array of symbols, the next argument in the list is not saved. It should be
     * used instead of NEWFUN when the symbol is the argument to equality */
    NEWFUN1,
    /** old function symbol, followed by its number in the array of symbols,
     *  the next argument in the list is not saved. It should be
     * used instead of OLDFUN when the symbol is the argument to equality */
    OLDFUN1,
    /** old variable, followed by its number in the array of variables,
     * the next argument in the list is not saved */
    OLDVAR1,
    /** positive literal in a list, followed by its number */
    PLIT,
    /** negative literal in a list, followed by its number */
    NLIT,
    /** clause */
    CLS,
    /** new predicate symbol, followed by its arity and number in the array of symbols */
    NEWPRED,
    /** old predicate symbol, followed by its number in the array of symbols */
    OLDPRED,
    /** end of code */
    END
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
