
/*
 * File ArithmeticIndex.hpp.
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
 * @file ArithmeticIndex.hpp
 * Defines class ArithmeticIndex.
 */

#ifndef __ArithmeticIndex__
#define __ArithmeticIndex__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Theory.hpp"

#include "Index.hpp"

namespace Indexing {

#if 0

using namespace Lib;
using namespace Kernel;

class ConstraintDatabase
: public ArithmeticKB
{
public:
  ConstraintDatabase();

  void handleLiteral(Literal* lit, bool adding, Clause* premise, bool negative=false);

  //overrides ArithmeticKB::isNonEqual
  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise);
  //overrides ArithmeticKB::isGreater
  bool isGreater(TermList t, InterpretedType val, Clause*& premise);
  //overrides ArithmeticKB::isLess
  bool isLess(TermList t, InterpretedType val, Clause*& premise);

  void reset()
  { _termConstraints.reset(); }

private:
  
  struct ConstraintInfo;
  
  Theory* theory;
  DHMap<TermList, ConstraintInfo*> _termConstraints;
};


class ArithmeticIndex
: public Index
{
public:
  ArithmeticIndex();

  void handleClause(Clause* c, bool adding);

  bool isNonEqual(TermList t, InterpretedType val, Clause*& premise)
  { return _db.isNonEqual(t, val, premise); }
  bool isGreater(TermList t, InterpretedType val, Clause*& premise)
  { return _db.isGreater(t, val, premise); }
  bool isLess(TermList t, InterpretedType val, Clause*& premise)
  { return _db.isLess(t, val, premise); }


private:
  ConstraintDatabase _db;
};
#endif
}

#endif // __ArithmeticIndex__
