/**
 * @file TermIteDefinitions.hpp
 * Defines class TermIteDefinitions.
 */

#ifndef __TermIteDefinitions__
#define __TermIteDefinitions__

#include "Forwards.hpp"


namespace Shell {

using namespace Kernel;

/**
 * A class with function @b apply() that eliminates all let...in and
 * term if-then-else expressions.
 *
 * Formula if-then-else expressions are not eliminated here but in
 * the @b FormulaIteExpander class.
 */
class SpecialTermElimination {
public:
  SpecialTermElimination();

  void apply(UnitList*& units);
  FormulaUnit* apply(FormulaUnit* fu, UnitList*& defs);
private:
  class LetSpec
  {
    bool _term;
    union {
      struct {
	size_t origin; //size_t here stands for TermList
	size_t target;
      } _t;
      struct {
	Literal* origin;
	Formula* target;
      } _f;
    };
  public:
    LetSpec(TermList o, TermList t) : _term(true)
    {
      CALL("SpecialTermElimination::LetSpec::LetSpec(TermList...)");
      ASS(o.isSafe());
      //here we assert that the origin is either variable or a function
      //applied to pairwise distinct variables
      ASS(!o.isTerm() || o.term()->weight()==o.term()->arity()+1);
      ASS(!o.isTerm() || o.term()->getDistinctVars()==o.term()->arity());

      _t.origin = o.content();
      _t.target = t.content();
    }
    LetSpec(Literal* o, Formula* t) : _term(false)
    {
      CALL("SpecialTermElimination::LetSpec::LetSpec(Literal*...)");
      //here we assert that the origin is a predicate applied to
      //pairwise distinct variables
      ASS_EQ(o->weight(),o->arity()+1);
      ASS_EQ(o->getDistinctVars(),o->arity());


      _f.origin = o;
      _f.target = t;
    }
    bool term() const { return _term; }
    TermList tOrigin() const { ASS(term()); return TermList(_t.origin); }
    TermList tTarget() const { ASS(term()); return TermList(_t.target); }
    Literal* fOrigin() const { ASS(!term()); return _f.origin; }
    Formula* fTarget() const { ASS(!term()); return _f.target; }
  };

  TermList processSpecialTerm(Term* t);

  TermList process(TermList t);
  Term* process(Term* t);
  Formula* process(Formula* f);
  FormulaList* process(FormulaList* fs);
  FormulaUnit* apply(FormulaUnit* fu);

  Term* eliminateTermIte(Formula * condition, TermList thenBranch, TermList elseBranch);

  bool checkForTermLetReplacement(TermList t, TermList& res);

  bool eliminatingTermLet() const { return _letStack.isNonEmpty() && _letStack.top().term(); }
  bool eliminatingFormulaLet() const { return _letStack.isNonEmpty() && !_letStack.top().term(); }
  bool eliminatingTermIte() const { return _letStack.isEmpty(); }

  UnitList* _defs;
  /**
   * For each let...in expression we put an entry on the stack and traverse its body
   * once with it on the stack and then when we remove it from the stack. When the
   * stack is empty, we perform elimination of the term-ite expressions.
   */
  Stack<LetSpec> _letStack;
};

}

#endif // __TermIteDefinitions__
