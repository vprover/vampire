
/*
 * File BFNT.hpp.
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
 * @file BFNT.hpp
 * Defines class BFNT used to implement the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */


#ifndef __BFNT__
#define __BFNT__

#include "Forwards.hpp"

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"

using namespace Kernel;

namespace Shell {

class Property;

/**
 * Class BFNT for implementing the transformation of clauses into
 * the EPR form described by Baumgartner, Fuchs, de Nivelle and Tinelli.
 * @since 30/07/2011 Manchester
 */
class BFNT
{
public:
  BFNT(Property* prop);
  void apply(UnitList* units);
  UnitList* create(unsigned modelSize);
  Problem* createProblem(unsigned modelSize);
private:
  Clause* apply(Clause* cl);
  static Clause* resolveNegativeVariableEqualities(Clause* cl);

  /** equality proxy symbol signature number */
  unsigned _proxy;
  /** map from function symbols to new predicate symbols denoting these functions */
  Map<unsigned,unsigned> _preds;
  /** transformed flat EPR clauses */
  Stack<Clause*> _flat;
  /** constants $1, $2, ... created to denote domain elements */
  Stack<Term*> _constants;
  // /** constants from the problem, used when the problem has no equality */
  // Set<Term*> _problemConstants;
  /** problem properties, passed in the constructor */
  // Property* _property; // MS: unused
};

};

#endif /* __BFNT__ */
