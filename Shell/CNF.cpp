/**
 * @file CNF.cpp
 * Implements class CNF implementing CNF transformation.
 * @since 19/01/2004 Manchester
 * @since 27/12/2007 Manchester, changed completely to a new implementation
 */

#include "../Debug/Tracer.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "CNF.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Initialise the CNF object.
 * @since 27/12/2007 Manchester
 */
CNF::CNF()
  : _literals(16),
    _formulas(16)
{
} // CNF::CNF

/**
 * Convert @b unit to CNF and push the resulting clauses on @b stack
 * @pre @b unit must be a formula unit
 * @since 27/12/2007 Manchester
 */
void CNF::clausify (Unit* unit,Stack<Clause*>& stack)
{
  CALL("CNF::clausify/2");
  ASS(! unit->isClause());

  _unit = static_cast<FormulaUnit*>(unit);
  _result = &stack;
  _literals.reset();
  _formulas.reset();

  Formula* f = _unit->formula();
  switch (f->connective()) {
  case TRUE:
    return;
  case FALSE:
    {
      // create an empty clause and push it in the stack
      Clause* clause = new(0) Clause(0,
				     unit->inputType(),
				     new Inference1(Inference::CLAUSIFY,unit));
      stack.push(clause);
    }
    return;
  default:
    clausify(f);
  }
} // CNF::clausify()


/**
 * Clausify the formula f \/ F1 \/ ... \/ Fn \/ L1 \/ ... \/ Lm,
 * where [F1,...,Fn] is the content of _formulas and [L1,...,Lm]
 * is the content of _literals. After the clausification restore
 * the stacks _formulas and _literals to their state before the call.
 *
 * @since 27/12/2007 Manchester
 */
void CNF::clausify (Formula* f)
{
  CALL("CNF::clausify/1");

  switch (f->connective()) {
  case LITERAL:
    _literals.push(f->literal());
    if (_formulas.isEmpty()) {
      // collect the clause
      int length = _literals.length();
      Clause* clause = new(length) Clause(length,
					  _unit->inputType(),
					  new Inference1(Inference::CLAUSIFY,
							 _unit));;
      for (int i = length-1;i >= 0;i--) {
	(*clause)[i] = _literals[i];
      }
      _result->push(clause);
    }
    else {
      f = _formulas.pop();
      clausify(f);
      _formulas.push(f);
    }
    _literals.pop();
    return;

  case AND:
    {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	clausify(fs.next());
      }
    }
    return;

  case OR:
    {
      int ln = _formulas.length();

      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	_formulas.push(fs.next());
      }
      clausify(_formulas.pop());
      _formulas.truncate(ln);
    }
    return;

  case FORALL:
    clausify(f->qarg());
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // CNF::clausify

// void CNF::clausify (Problem& problem, 
// 		    const FormulaList& formulas, 
// 		    const LiteralList& literals,
// 		    const Unit& parent)
// {
//   if (formulas.isEmpty()) {
//     Clause c(literals);
//     problem.giveUnits().addFirst(Unit(Inference::CLAUSIFY,c,parent));
//     return;
//   }

//   // formulas is non-empty
//   Formula f(formulas.head());
//   FormulaList fs(formulas.tail());

//   switch (f.connective()) {
//   case ATOM: 
//     clausify(problem, fs, 
// 	     LiteralList(Literal(true, f.atom()),literals), 
// 	     parent);
//     return;

//   case NOT: 
//     clausify(problem, fs, 
// 	     LiteralList(Literal(false, f.uarg().atom()), literals), 
// 	     parent);
//     return;

//   case OR: 
//     {
//       FormulaList newFs(f.args());
//       newFs.append(fs);
//       clausify (problem, newFs, literals, parent);
//       return;
//     }

//   case AND:
//     {
//       VL::Iterator<Formula> args(f.args());
//       while (args.hasNext()) {
// 	FormulaList newFs(args.next(), fs);
// 	clausify(problem,newFs,literals,parent);
//       }
//       return;
//     }

//   case TRUE:
//     return;

//   case FALSE:
//     clausify(problem,fs,literals,parent);
//     return;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // CNF::clausify

