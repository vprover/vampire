
/*
 * File EquivalentVariableRemover.hpp.
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
 * @file EquivalentVariableRemover.hpp
 * Defines class EquivalentVariableRemover.
 */

#ifndef __EquivalentVariableRemover__
#define __EquivalentVariableRemover__
#if GNUMP

#include <utility>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"

namespace Shell {

using namespace std;
using namespace Lib;
using namespace Kernel;

class EquivalentVariableRemover {
public:
  EquivalentVariableRemover();

  bool apply(ConstraintRCList*& lst);
private:
  void reset();
  void scan(ConstraintRCList* lst);

  Var getRoot(Var v) { return _eqClasses.root(v); }
  bool remainsSame(Var v) { return getRoot(v)==v; }
  bool remainsSame(Constraint& c);

  struct VarMapper;

  typedef pair<Var,Var> VarPair;
  enum PairStatus {
    FIRST_POS = 1,
    FIRST_NEG = -1,
    BOTH = 0
  };
  DHMap<VarPair, PairStatus> _pairs;
  IntUnionFind _eqClasses;
  bool _haveEquivalences;
};

}
#endif //GNUMP
#endif // __EquivalentVariableRemover__
