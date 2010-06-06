/**
 * @file Unit.hpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Unit__
#define __Unit__

#include <string>

#include "Forwards.hpp"

#include "Lib/List.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;

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
  /** set the input type of the unit */
  void setInputType(InputType it)
  { _inputType=it; }

  /** Return the number of this unit */
  unsigned number() const { return _number; }

  /** Return the inference of this unit */
  Inference* inference() { return _inference; }
  /** Return the inference of this unit */
  const Inference* inference() const { return _inference; }
  /** the input unit number this clause is generated from, -1 if none */
  int adam() const {return _adam;}

  /** Return the inherited color of the unit, computing it if necessary */
  inline Color inheritedColor() const
  {
    return static_cast<Color>(_inheritedColor);
  }
  void setInheritedColor(Color color)
  {
    ASS_NEQ(color,COLOR_INVALID);
    _inheritedColor = color;
  } // setInheritedColor

  Color getColor();
  Formula* getFormula(BDDNode* prop);

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

  /** mark the unit as read from a TPTP included file  */
  inline void markIncluded() {_included = 1;}
  /** true if the unit is read from a TPTP included file  */
  inline bool included() const {return _included;}

  /** Return true iff unit was created during preprocessing
   * (and not during the run of the saturation algorithm) */
  inline bool isFromPreprocessing()
  { return !_firstNonPreprocessingNumber || _number<_firstNonPreprocessingNumber; }

  static void onPreprocessingEnd();

protected:
  /** Number of this unit, used for printing and statistics */
  unsigned _number;
  /** Kind  */
  unsigned _kind : 1;
  /** input type  */
  unsigned _inputType : 2;
  /** used in interpolation to denote parents of what color have been used */
  unsigned _inheritedColor : 2;
  /** true if the unit is read from a TPTP included file  */
  unsigned _included : 1;
  /** inference used to obtain the unit */
  Inference* _inference;
  /** the input unit number this clause is generated from, -1 if none */
  int _adam;

  Unit(Kind kind,Inference* inf,InputType it);

  /** Used to enumerate units */
  static unsigned _lastNumber;

  /** Used to determine which clauses come from preprocessing
   *
   * 0 means preprocessing is not over yet.*/
  static unsigned _firstNonPreprocessingNumber;
}; // class Unit

}
#endif
