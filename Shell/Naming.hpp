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
 * @file Naming.hpp
 * Defines the naming technique
 * @since 05/05/2005 Manchester
 * @since 07/07/2007 Manchester, changed to new datastructures
 */

#ifndef __Naming__
#define __Naming__

#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/List.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing the naming technique.
 * @since 05/05/2005 Manchester
 */
class Naming
{
public:
  Naming (int threshold, bool preserveEpr, bool appify);
  FormulaUnit* apply(FormulaUnit* unit,UnitList*& defs);
private:
  /** Encodes information about the position of the sub formula */
  enum Where {
    /** the subformula is only in the range of conjunctions */
    ON_TOP,
    /** the subformula is in the range of at least one equivalence */
    UNDER_IFF,
    /** the subformula has a positive polarity but has at least one
     * disjunction above */
    OTHER
  };

  /** Encodes phases in the iterative processing (see apply_iter)
   * of the originally recursive (see apply_sub and apply_list) algorithm */
  enum ApplyWhat {
    APPLY_SUB_TOP,
    APPLY_SUB_AND,
    APPLY_SUB_OR,
    APPLY_SUB_IFFXOR,
    APPLY_SUB_FORALLEXISTS,
    APPLY_LIST_TOP,
    APPLY_LIST_POST
  };

  /** Encode what apply_sub returns (where pos and neg were originally passed by reference) */
  struct ResultSub {
    int pos;
    int neg;
    Formula* res;
  };

  /** Encode what apply_list returns (results and negResults live on heap) */
  struct ResultList {
    FormulaList* res;
  };

  /** Encode either ResultSub or ResultList*/
  union Result {
    ResultSub  resSub;
    ResultList resList;
  };

  /** Store local variables to survive recursive calls -- for the AND/OR sub-case*/
  struct SubtaskAndOr {
    int* cls;
    int* negCls;
  };

  /** Store local variables to survive recursive calls -- for the FORALL/EXISTS sub-case*/
  struct SubtaskForallExists {
    bool varFlagSet;
  };

  /** Store apply_sub input and local variables */
  struct TaskApplySub {
    Formula* f;
    Where where;
    union {
      SubtaskAndOr taskAndOr;
      SubtaskForallExists taskForallExists;
    };
  };

  /** Store apply_list input and local variables */
  struct TaskApplyList {
    FormulaList* fs;
    Where where;
    int* results;
    int* negResults;
  };

  /** Encode data needed for simulating a recursive of either apply_sub or apply_list. */
  struct Task {
    ApplyWhat fncTag;  // distinguish the two cases
    union {
      TaskApplySub  taskApplySub;
      TaskApplyList taskApplyList;
    };
  };

  /** Threshold for naming. If a non-unit clause is going to be used 
   *  the number of times greater than of equal to the threshold, 
   *  it will be named. 
   */
  int _threshold;
  /**
   * Marks if we want to avoid causing introduction of any non-zero
   * arity skolem functions
   *
   * Corresponds to the value of the epr_preserving_naming option.
   */
  bool _preserveEpr;
  bool _appify; // higher-order stuff
  /**
   * True if there are universally quantified variables at the scope of the current formula
   *
   * This value is maintained in the @b apply(Formula,Where,int&,int&) function
   * if the @b _preserveEpr value is true.
   */
  bool _varsInScope;

  bool canBeInDefinition(Formula* f,Where where);

  /** The list of definitions produced by naming for this unit*/
  UnitList* _defs;

  // set of already-introduced definitions (when -dr on), and whether they are iff
  DHMap<Literal *, bool> _already_seen;

  /** Replaces the two functions below with a non-recursive implementation. */
  Formula* apply_iter(Formula* top_f);

  Formula* apply_sub(Formula* subformula,Where where,int& pos,int& neg);
  FormulaList* apply_list(FormulaList* subformulas,
		     Where where,
		     int* results,
		     int* resultsNeg);
  Formula* introduceDefinition(Formula* f,bool iff);

  Literal* getDefinitionLiteral(Formula* f, VList* freeVars);
}; // class Naming

}

#endif
