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
 * @file SymCounter.hpp
 * Defines class SymCounter counting occurrences of
 * function and predicate symbols.
 *
 * @since 01/05/2002, Manchester
 */

#ifndef __sym_counter__
#define __sym_counter__

#include "Kernel/Unit.hpp"

namespace Kernel {
  class Signature;
  class Formula;
  class Clause;
  class Term;
  class TermList;
  class Literal;
}

using namespace Kernel;

namespace Shell {

/**
 * Class designed to count various kinds of occurrence of symbols
 * in a problem (unit, formula etc.)
 */
class SymCounter
{
 public:

  class FunOrTypeCon {
    int _occ;
   public:
    FunOrTypeCon () : _occ(0) {}
    int occ () const { return _occ; }
    void add (int add) { _occ += add; }
  };

  class Pred {
    int _pocc;  // positive occurrences
    int _nocc;  // negative occurrences
    int _docc;  // double occurrences (under equivalence)
   public:
    Pred ()
      : _pocc (0),
        _nocc (0),
        _docc (0)
        {}
    int pocc () const { return _pocc; }
    int nocc () const { return _nocc; }
    int docc () const { return _docc; }
    void add (int polarity, int add);
  };

  explicit SymCounter (Signature&);
  ~SymCounter ();

  // counting functions
  void count(UnitList*, int);
  void count(Formula*, int);
  void count(Clause*, int);
  void count(Formula*, int polarity, int add);
  void count(Literal*, int polarity, int add);
  void count(Term* term, int polarity, int add);

  /** Return information about n-th predicate symbol */
  Pred& getPred (int n)
  {
    ASS(n < _noOfPreds);
    return _preds[n];
  }
  /** Return information about n-th function symbol */
  FunOrTypeCon& getFun (int n)
  {
    ASS(n < _noOfFuns);
    return _funs[n];
  }
  /** Return information about n-th function symbol */
  FunOrTypeCon& getTypeCon (int n)
  {
    ASS(n < _noOfTypeCons);
    return _typeCons[n];
  }

 private:
  // structure
  /** Number of predicate symbols in the signature */
  int _noOfPreds;
  /** Number of function symbols in the signature */
  int _noOfFuns;
  /** Number of type constructor symbols in the signature */
  int _noOfTypeCons;
  /** Array to predicate counters */
  Pred* _preds;
  /** Array to function counters */
  FunOrTypeCon* _funs;
  /** Array to function typeCons */
  FunOrTypeCon* _typeCons;
}; // class SymCounter

}

#endif // __sym_counter__
