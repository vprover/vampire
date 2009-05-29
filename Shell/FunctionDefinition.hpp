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

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"
#include "../Lib/MultiCounter.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/Unit.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

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

  void removeAllDefinitions(UnitList* units);


  void scan(const UnitList* units);
  /** true if any definition has been found, must only be called
   *  after scan() */
  bool definitionFound() const
  { return _defs.size()!=0; }
  static Def* isFunctionDefinition (Unit&);
  static void deleteDef(Def* def);

//   int removeAllDefinitions ();
//   static bool isFunctionDefinition (const Clause&, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Literal*, Term*& lhs, Term*& rhs);
//   static bool isFunctionDefinition (const Formula&, Term*& lhs, Term*& rhs);

private:
  static Def* isFunctionDefinition (Clause*);
  static Def* isFunctionDefinition (FormulaUnit&);
  static Def* isFunctionDefinition (Literal*);
  static Def* defines (Term* lhs, Term* rhs);
  static bool occurs (unsigned function, Term&);


  bool isDefined(Term* t);
  Term* applyDefinition(Term* t);
  TermList applyDefinition(unsigned fn, TermList* argArr);

  typedef pair<unsigned,unsigned> BindingSpec;
  typedef DHMap<BindingSpec, TermList, IntPairSimpleHash> BindingMap;
  typedef DHMap<BindingSpec, bool, IntPairSimpleHash> UnfoldedSet;

  struct UnfoldingTaskRecord
  {
    enum Type {
      UNFOLD_DEFINITION,
      EVAL_BINDING_ARGUMENT
    };

    UnfoldingTaskRecord(Def* def) : type(UNFOLD_DEFINITION), def(def) {}
    UnfoldingTaskRecord(BindingSpec spec) : type(EVAL_BINDING_ARGUMENT), bSpec(spec) {}

    Type type;
//    union {
      Def* def;
      BindingSpec bSpec;
//    };
  };

  BindingMap bindings;
  UnfoldedSet unfolded;
  unsigned nextDefIndex;
  Stack<UnfoldingTaskRecord> tasks;
  Stack<unsigned> defIndexes;
  Stack<Def*> unfoldedDefs;
  /**
   * Terms that to be unfolded.
   * When zero element appears on the stack, a task from @b tasks stack
   * should be finished.
   */
  Stack<TermList*> toDo;
  Stack<Term*> terms;
  Stack<bool> modified;
  Stack<TermList> args;

  void finishTask();
  TermList evalVariableContent(unsigned var);
  void replaceByDefinition(Term* t);
  Term* applyDefinitions(Term* t);

  void unfoldDefinitions(Def* t);

//   void count (const Clause& c);
//   bool unfoldAllDefs ();
//   bool unfold (Def& def);
//   bool unfold (Term* t,UnitList* parents);
//   bool unfoldList (Term* ts,UnitList& parents);

//   void apply (LiteralList& ls,UnitList& parents);
//   void apply (Literal& l,UnitList& parents);
//   void apply (TermList& ls,UnitList& parents);
//   void apply (Term& l,UnitList& parents);

  typedef DHMap<int, Def*> Fn2DefMap;
  Fn2DefMap _defs;

//  /** Set storing all function definitions */
//  Stack<Def*> _defStore;
  /** Counters for occurrences of function symbols */
  MultiCounter _counter;
  /** The number of found definitions */
  int _found;
  /** The number of removed definitions */
  int _removed;
}; // class FunctionDefinition


}

#endif
