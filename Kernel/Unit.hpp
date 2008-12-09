/**
 * @file Unit.hpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Unit__
#define __Unit__

#include <string>
#include "../Lib/List.hpp"

using namespace std;
using namespace Lib;

namespace Kernel {

class Inference;

/**
 * Class to represent units of inference (such as clauses and formulas).
 * @since 08/05/2007 Manchester
 */
class Unit
{
public:
  /** Kind of unit. The integers should not be changed, they are used in
   *  Compare.
   */
  enum Kind {
    /** Clause unit */
    CLAUSE = 0,
    /** Formula unit */
    FORMULA = 1
  };

  /** Kind of input. The integers should not be changed, they are used in
   *  Compare. */
  enum InputType {
    /** Axiom or derives from axioms */
    AXIOM = 0,
    /** Assumption or derives from axioms and assumptions */
    ASSUMPTION = 1,
    /** Derived from lemma */
    LEMMA = 2,
    /** derives from the goal */
    CONJECTURE = 3
  };

  virtual ~Unit() {}

  virtual void destroy() = 0;
  virtual string toString() const = 0;

  string inferenceAsString() const;

  /** True if a clause unit */
  bool isClause() const
  { return _kind == CLAUSE; }

  /** return the input type of the unit */
  InputType inputType() const
  { return (InputType)_inputType; }

  /** Return the number of this unit */
  unsigned number() const { return _number; }

  /** Return the inference of this unit */
  Inference* inference() { return _inference; }
  /** Return the inference of this unit */
  const Inference* inference() const { return _inference; }
  /** the input unit number this clause is generated from, -1 if none */
  int adam() const {return _adam;}

  /**
   * Increase the number of references to the unit.
   *
   * Only clauses are reference-counted, so the base implementation
   * does nothing.
   */
  virtual void incRefCnt() {}
  /**
   * Decrease the number of references to the unit.
   *
   * Only clauses are reference-counted, so the base implementation
   * does nothing.
   */
  virtual void decRefCnt() {}

protected:
  /** Number of this unit, used for printing and statistics */
  unsigned _number;
  /** Kind  */
  unsigned _kind : 1;
  /** iput type  */
  unsigned _inputType : 2;
  /** inference used to obtain the unit */
  Inference* _inference;
  /** the input unit number this clause is generated from, -1 if none */
  int _adam;

  Unit(Kind kind,Inference* inf,InputType it);

  /** Used to enumerate units */
  static unsigned _lastNumber;
}; // class Unit

typedef List<Unit*> UnitList;

}
#endif
