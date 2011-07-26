/**
 * @file Shell/TPTP.cpp
 * Implements class TPTP for printing various objects in the TPTP syntax.
 *
 * @since 12/04/2008 Manchester
 */

#include "Lib/Int.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"

#include "Parse/TPTP.hpp"

#include "TPTP.hpp"

using namespace std;
using namespace Kernel;
using namespace Shell;

string TPTP::toString(const Formula* f)
{
  CALL("TPTP::toString(const Formula*)");
  static string names [] =
    { "", " & ", " | ", " => ", " <=> ", " <~> ",
      "~", "!", "?", "", "", "", "$false", "$true"};
  ASS_EQ(sizeof(names)/sizeof(string), TRUE+1);
  Connective c = f->connective();
  string con = names[(int)c];
  switch (c) {
  case LITERAL:
    return f->literal()->toString();
  case AND:
  case OR:
    {
      const FormulaList* fs = f->args();
      string result = "(" + toString(fs->head());
      fs = fs->tail();
      while (! fs->isEmpty()) {
	result += con + toString(fs->head());
	fs = fs->tail();
      }
      return result + ")";
    }

  case IMP:
  case IFF:
  case XOR:
    return string("(") + toString(f->left()) +
           con + toString(f->right()) + ")";

  case NOT:
    return string("(") + con + toString(f->uarg()) + ")";

  case FORALL:
  case EXISTS:
    {
      string result = string("(") + con + "[";
      const Formula::VarList* vars = f->vars();
      result += 'X';
      result += Int::toString(vars->head());
      vars = vars->tail();
      while (! vars->isEmpty()) {
	result += ',';
	result += 'X';
	result += Int::toString(vars->head());
	vars = vars->tail();
      }
      return result + "] : (" + toString(f->qarg()) + ") )";
    }
  case FALSE:
  case TRUE:
    return con;
  default:
    ASSERTION_VIOLATION;
  }
  return "formula";
}

/**
 * Output unit in TPTP format
 *
 * If the unit is a formula of type @b CONJECTURE, output the
 * negation of Vampire's internal representation with the
 * TPTP role conjecture. If it is a clause, just output it as
 * is, with the role negated_conjecture.
 */
string TPTP::toString (const Unit* unit)
{
  CALL("TPTP::toString(const Unit*)");
//  const Inference* inf = unit->inference();
//  Inference::Rule rule = inf->rule();

  string prefix;
  string main = "";

  bool negate_formula = false;
  string kind;
  switch (unit->inputType()) {
  case Unit::ASSUMPTION:
    kind = "hypothesis";
    break;

  case Unit::CONJECTURE:
    if(unit->isClause()) {
      kind = "negated_conjecture";
    }
    else {
      negate_formula = true;
      kind = "conjecture";
    }
    break;

  default:
    kind = "axiom";
    break;
  }

  if (unit->isClause()) {
    prefix = "cnf";
    main = static_cast<const Clause*>(unit)->toTPTPString();
  }
  else {
    prefix = "fof";
    const Formula* f = static_cast<const FormulaUnit*>(unit)->formula();
    if(negate_formula) {
      Formula* quant=Formula::quantify(const_cast<Formula*>(f));
      if(quant->connective()==NOT) {
	ASS_EQ(quant, f);
	main = toString(quant->uarg());
      }
      else {
	Formula* neg=new NegatedFormula(quant);
	main = toString(neg);
	neg->destroy();
      }
      if(quant!=f) {
	ASS_EQ(quant->connective(),FORALL);
	static_cast<QuantifiedFormula*>(quant)->vars()->destroy();
	quant->destroy();
      }
    }
    else {
      main = toString(f);
    }
  }

  string unitName;
  if(!Parse::TPTP::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }

  return prefix + "(" + unitName + "," + kind + ",\n"
    + "    " + main + ").\n";
}

