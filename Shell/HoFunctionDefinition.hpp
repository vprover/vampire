
/*
 * File HoFunctionDefinition.hpp.
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
 * @file HoFunctionDefinition.hpp
 * Defines class HoFunctionDefinition that unfolds higher-order definitions
 * that have been MARKED AS DEFINITIONS in the input. This requires changing 
 * in the future once a robust understnading of what is a higher-order 
 * definition has been achieved. Definition undfolding and beta-reduction 
 * are carried out in a single step.
 */

#ifndef __HoFunctionDefinition__
#define __HoFunctionDefinition__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Unit.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * A higher-order function definition is
 * any unit that has been marked as a "definition" in the input.
 * In general we would expect such a unit to be off the form:
 *
 * ^^^^constant(t_1 ... t_n) = term, where t_1 to t_n are Du Bruijn indices
 * (in eta-long form) and:
 * 1) term does not contain constant
 * 2) term contains no variables.
 *
 * we check to ensure that the definition is off this form.
 */
class HoFunctionDefinition
{
public:
  HoFunctionDefinition();
  ~HoFunctionDefinition();

  struct HoDef;
  
  void removeAllDefinitions(Problem& prb);
  bool removeAllDefinitions(UnitList*& units);

//   int removeAllDefinitions ();
//   static bool isFunctionDefinition (const Clause&, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Literal*, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Formula&, Term*& lhs, Term*& rhs);

private:
  
  bool isSafe(HoDef* def);
  static HoDef* isFunctionDefinition (Clause*);
  /*static Def* isFunctionDefinition (FormulaUnit&); */
  static HoDef* isFunctionDefinition (Literal*);
  static HoDef* defines (Term* lhs, Term* rhs);
  /*static bool occurs (unsigned function, Term&); */
 
  static int isEtaExpandedFunctionSymbol(Term*); 
  static bool isValidDefinens(Term*, unsigned, Stack<unsigned>&);

  Term* unfoldDefs(Term* term);
  
  Clause* applyDefinitions(Clause* cl);
  Term* applyDefinitions(Literal* lit, Stack<HoDef*>* usedDefs);
  
  typedef DHMap<int, HoDef*> Fn2DefMap;
  Fn2DefMap _defs;
  
  DHSet<unsigned> _safeFunctors;
  
  Stack<HoDef*> _safeDefs;
  Stack<unsigned> _possiblyUnsafeFunctors;
}; // class FunctionDefinition


}

#endif
