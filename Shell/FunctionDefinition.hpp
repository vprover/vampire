/**
 * @file FunctionDefinition.hpp
 * Defines class FunctionDefinition implementing work with definitions.
 *
 * @since 28/05/2004 Manchester
 * @note There is a lot of confusion in the definition handling 
 *       mechanism of Vampire. There is much in common between
 *       this class and class Definition and they should be reworked.
 *       In addition, Preprocess eliminates unused definitions
 *       only from FO (not clausal) problems. Why? Options do
 *       not separate function and predicate definitions. This
 *       should be re-thought and re-implemented but it is too
 *       close to CASC now to make big changes.
 */

#ifndef __FunctionDefinition__
#define __FunctionDefinition__

#include "../Lib/Stack.hpp"
#include "../Lib/MultiCounter.hpp"
#include "../Kernel/Unit.hpp"

namespace Kernel {
  class Term;
  class Literal;
  class Literal;
  class FormulaUnit;
  class Clause;
}

using namespace Lib;
using namespace Kernel;

namespace Shell {

/**
 * Class implementing procedures related to function
 * definitions. A function definition is of the form
 * f(x1,...,xn) = t, where 
 * <ol>
 *  <li>all variables of t occur in {x1,...,xn}; </li>
 *  <li>f does not occur in t.</li>
 *  <li>if f is a constant, then t is a constant, too.
 * </ol>
 * @since 29/05/2004 Manchester
 */
class FunctionDefinition
{
public:
  class Def;
  FunctionDefinition();
  ~FunctionDefinition();
  void scan(const UnitList* units);
  /** true if any definition has been found, must only be called
   *  after scan() */
  bool definitionFound() const
  { return _defs.isNonEmpty(); }
  static Def* isFunctionDefinition (const Unit&);
  static void deleteDef(Def* def);

//   int removeAllDefinitions ();
//   static bool isFunctionDefinition (const Clause&, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Literal*, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Formula&, Term*& lhs, Term*& rhs);

private:
  static Def* isFunctionDefinition (const Clause&);
  static Def* isFunctionDefinition (const FormulaUnit&);
  static Def* isFunctionDefinition (const Literal*);
  static Def* defines (const Term* lhs, const Term* rhs);
  static bool occurs (unsigned function, const Term&);

//   void count (const Clause& c);
//   bool unfoldAllDefs ();
//   bool unfold (Def& def);
//   bool unfold (Term* t,UnitList* parents);
//   bool unfoldList (Term* ts,UnitList& parents);

//   void apply (LiteralList& ls,UnitList& parents);
//   void apply (Literal& l,UnitList& parents);
//   void apply (TermList& ls,UnitList& parents);
//   void apply (Term& l,UnitList& parents);

  /** Set storing all function definitions */
  Stack<Def*> _defs;
  /** Counters for occurrences of function symbols */
  MultiCounter _counter;
  /** The number of found definitions */
  int _found;
  /** The number of removed definitions */
  int _removed;
}; // class FunctionDefinition


}

#endif
