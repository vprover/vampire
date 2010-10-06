/**
 * @file Property.cpp (syntactic properties of problems)
 *
 * @since 06/06/2001 Manchester
 * @author Andrei Voronkov
 * @since 17/07/2003 Manchester, changed to new representation
 */

#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"

#include "FunctionDefinition.hpp"
#include "Property.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Initialize Property. Must be applied to the preprocessed problem.
 *
 * @since 29/06/2002, Manchester
 */
Property::Property ()
  : _goalClauses (0),
    _axiomClauses (0),
    _positiveEqualityAtoms (0),
    _equalityAtoms (0),
    _atoms (0),
    _goalFormulas (0),
    _axiomFormulas (0),
    _subformulas (0),
    _terms (0),
    _unitGoals (0),
    _unitAxioms (0),
    _hornGoals (0),
    _hornAxioms (0),
    _equationalClauses (0),
    _pureEquationalClauses (0),
    _groundUnitAxioms (0),
    _positiveAxioms (0),
    _groundPositiveAxioms (0),
    _groundGoals (0),
    _maxFunArity (0),
    _maxPredArity (0),
    _totalNumberOfVariables (0),
    _maxVariablesInClause (0),
    _props(0)
{
} // Property::Property


/**
 * Scan property from a problem.
 * @since 29/06/2002 Manchester
 */
void Property::scan(UnitList* units)
{
  CALL("Property::scan(UnitList*)");

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    scan(us.next());
  }
  // determine the category
  if (formulas() > 0) { // FOF, either FEQ or FNE
    if (_equalityAtoms == 0) {
      _category = FNE;
    }
    else {
      _category = FEQ;
    }
  }
  // no formulas in the input, one of NEQ, HEQ, PEQ, HNE, NNE, EPR, UEQ
  else if (_maxFunArity == 0) { // all function symbols are constants
    if (_pureEquationalClauses == clauses()) { // only equations, UEQ or PEQ
      if (clauses() == unitClauses()) { // all clauses are unit
	_category = UEQ;
      }
      else {
	_category = PEQ;
      }
    }
    else {
      _category = EPR;
    }
  }
  // one of NEQ, HEQ, PEQ, HNE, NNE, UEQ
  else if (_equationalClauses == 0 ) { // HNE, NNE
    if (clauses() == hornClauses()) { // all clauses are horn
      _category = HNE;
    }
    else {
      _category = NNE;
    }
  }
  // one of NEQ, HEQ, PEQ, UEQ
  else if (_pureEquationalClauses == clauses()) { // only equations, UEQ or PEQ
    if (clauses() == unitClauses()) { // all clauses are unit
      _category = UEQ;
    }
    else {
      _category = PEQ;
    }
  }
  // one of NEQ, HEQ
  else if (clauses() == hornClauses()) { // all clauses are horn
    _category = HEQ;
  }
  else {
    _category = NEQ;
  }
} // Property::scan(const UnitList* units)


/**
 * Scan property from a unit.
 *
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types,
 *        formula scanning added
 * @since 26/05/2007 Manchester, changed to use new datastructures
 */
void Property::scan (Unit* unit)
{
  CALL("Property::scan(const Unit*)");

  if (unit->isClause()) {
    scan(static_cast<Clause*>(unit));
  }
  else {
    scan(static_cast<FormulaUnit*>(unit));
  }
  if (! hasProp(PR_HAS_FUNCTION_DEFINITIONS)) {
    FunctionDefinition::Def* def =
      FunctionDefinition::isFunctionDefinition(*unit);
    if (def) {
      addProp(PR_HAS_FUNCTION_DEFINITIONS);
      FunctionDefinition::deleteDef(def);
    }
  }
} // Property::scan (const Unit* unit)

/**
 * Scan a clause.
 *
 * @param clause the clause
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types
 * @since 27/08/2003 Vienna, changed to count variables
 * @since 26/05/2007 Manchester, changed to use new datastructures
 */
void Property::scan (Clause* clause)
{
  CALL("Property::scan (const Clause*)");

  int positiveLiterals = 0;
  int negativeLiterals = 0;
  int equationalLiterals = 0;
  int positiveEquationalLiterals = 0;
  int groundLiterals = 0;
  _variablesInThisClause = 0;

  for (int i = clause->length()-1;i >= 0;i--) {
    Literal* literal = (*clause)[i];
    if (literal->isPositive()) {
      positiveLiterals ++;
    }
    else {
      negativeLiterals ++;
    }

    if (literal->isEquality()) {
      equationalLiterals++;
      if (literal->isPositive()) {
	positiveEquationalLiterals++;
      }
    }

    bool isGround = true;
    scan(literal,isGround);

    if (isGround) {
      groundLiterals++;
    }
  }
  int literals = positiveLiterals + negativeLiterals;
  _atoms += literals;

  if ( equationalLiterals > 0 ) {
    _equationalClauses ++;
    _equalityAtoms += equationalLiterals;
    _positiveEqualityAtoms += positiveEquationalLiterals;
  }
  if ( literals == equationalLiterals ) {
    _pureEquationalClauses ++;
  }

  if (clause->inputType() == Unit::AXIOM) {
    _axiomClauses ++;
    if ( literals == 1) {
      _unitAxioms ++;
      if ( groundLiterals == 1) {
	_groundUnitAxioms ++;
      }
    }
    if (positiveLiterals <= 1) {
      _hornAxioms ++;
    }
    if (negativeLiterals == 0) {
      _positiveAxioms ++;
      if (literals == groundLiterals) {
	_groundPositiveAxioms ++;
      }
    }
  }
  else {
    _goalClauses ++;
    if ( literals == 1) {
      _unitGoals ++;
    }
    if (positiveLiterals <= 1) {
      _hornGoals ++;
    }
    if (literals == groundLiterals) {
      _groundGoals ++;
    }
  }

  _totalNumberOfVariables += _variablesInThisClause;
  if (_variablesInThisClause > _maxVariablesInClause) {
    _maxVariablesInClause = _variablesInThisClause;
  }
  if (! hasProp(PR_HAS_X_EQUALS_Y) && hasXEqualsY(clause)) {
    addProp(PR_HAS_X_EQUALS_Y);
  }
} // Property::scan (const Clause* clause, bool isAxiom)


/**
 * Scan a formula unit.
 * @since 27/05/2007 flight Manchester-Frankfurt
 */
void Property::scan (FormulaUnit* unit)
{
  CALL("Property::scan (const FormulaUnit*)");

  if (unit->inputType() == Unit::AXIOM) {
    _axiomFormulas ++;
  }
  else {
    _goalFormulas++;
  }
  Formula* f = unit->formula();
  scan(f);
  if (! hasProp(PR_HAS_X_EQUALS_Y)) {
    MultiCounter vc;
    if (hasXEqualsY(f,vc,1)) {
      addProp(PR_HAS_X_EQUALS_Y);
    }
  }
} // Property::scan


/**
 * Scan a formula.
 *
 * @since 17/07/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
void Property::scan (Formula* formula)
{
  CALL("void Property::scan (const Formula&)");

  SubformulaIterator fs(formula);
  while (fs.hasNext()) {
    _subformulas++;
    Formula* f = fs.next();
    if (f->connective() == LITERAL) {
      _atoms++;
      Literal* lit = f->literal();
      if (lit->isEquality()) {
	_equalityAtoms++;
	if (lit->isPositive()) {
	  _positiveEqualityAtoms++;
	}
      }
      bool dummy = false;
      scan(lit,dummy);
    }
  }
} // Property::scan (const Formula&)


/**
 * Scan a literal.
 *
 * @param lit the literal
 * @param isGround will be set to false if the literal contains a variable
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types
 * @since 27/05/2007 flight Manchester-Frankfurt, uses new datastructures
 */
void Property::scan (Literal* lit, bool& isGround)
{
  CALL("Property::scan (const Literal*...)");

  if (! lit->isEquality()) {
    int arity = lit->arity();
    if (arity > _maxPredArity) {
      _maxPredArity = arity;
    }
  }

  scan(lit->args(),isGround);

  if(!hasProp(PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION) && lit->isEquality()
	  && lit->isNegative() && !isGround) {
    if( ( lit->nthArgument(0)->isVar() &&
	    !lit->nthArgument(1)->containsSubterm(*lit->nthArgument(0)) ) ||
	( lit->nthArgument(1)->isVar() &&
    	    !lit->nthArgument(0)->containsSubterm(*lit->nthArgument(1)) )) {
      addProp(PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION);
    }
  }
} // Property::scan (const Atom& term, bool& isGround)


/**
 * Scan a term arguments.
 *
 * @param ts the list of terms
 * @param isGround will be set to false if the term contains a variable
 * @since 29/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types,
 *        also NUMERIC case added
 * @since 27/08/2003 Vienna, changed to count variables
 * @since 27/05/2007 flight Manchester-Frankfurt, changed to new datastructures
 */
void Property::scan(TermList* ts, bool& isGround)
{
  CALL("Property::scan(TermList*))");

  Stack<TermList*> stack(64);

  for (;;) {
    if (ts->isEmpty()) {
      if (stack.isEmpty()) {
	return;
      }
      ts = stack.pop();
    }
    // ts is non-empty
    _terms ++;
    if (ts->isVar()) {
      isGround = false;
      _variablesInThisClause++;
    }
    else { // ts is a reference to a complex term
      Term* t = ts->term();
      int arity = t->arity();
      if (arity > _maxFunArity) {
	_maxFunArity = arity;
      }
      TermList* ss = t->args();
      if (! ss->isEmpty()) {
	stack.push(ss);
      }
    }
    ts = ts->next();
  }
} // Property::scan (const Term& term, bool& isGround)


/**
 * Return the string representation of the CASC category.
 */
string Property::categoryString() const
{
  CALL("string Property::categoryString() const");

  switch (_category)
    {
    case NEQ:
      return "NEQ";
    case HEQ:
      return "HEQ";
    case PEQ:
      return "PEQ";
    case HNE:
      return "HNE";
    case NNE:
      return "NNE";
    case FEQ:
      return "FEQ";
    case FNE:
      return "FNE";
    case EPR:
      return "EPR";
    case UEQ:
      return "UEQ";
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return "";
#endif
    }
} // categoryString


/**
 * Output the property to a string readable by a human. NOT ALL FIELDS
 * ARE CURRENTLY OUTPUT.
 * @since 27/08/2003 Vienna
 */
string Property::toString () const
{
  string result("TPTP class: ");
  result += categoryString() + "\n";

  if (clauses() > 0) {
    result += "Clauses: ";
    result += Int::toString(clauses());
    result += " (";
    result += Int::toString(_unitAxioms+_unitGoals);
    result += " unit, ";
    result += Int::toString(_goalClauses);
    result += " goal, ";
    result += Int::toString(_equationalClauses);
    result += " equational)\n";

    result += "Variables: ";
    result += Int::toString(_totalNumberOfVariables);
    result += " (";
    result += Int::toString(_maxVariablesInClause);
    result += " maximum in a single clause)\n";
  }

  if (formulas() > 0) {
    result += "Formulas: ";
    result += Int::toString(formulas());
    result += " (";
    result += Int::toString(_goalFormulas);
    result += " goal)\n";
    result += "Subformulas: ";
    result += Int::toString(_subformulas);
    result += "\n";
  }

  result += "Atoms: ";
  result += Int::toString(_atoms);
  result += " (";
  result += Int::toString(_equalityAtoms);
  result += " equality)\n";

  return result;
} // Property::toString


/**
 * True if the clause contains a positive literal X=Y.
 * @since 04/06/2004 Manchester
 * @since 27/05/2007 Frankfurt airport, changed to new datastructures
 */
bool Property::hasXEqualsY (const Clause* c)
{
  CALL("Property::hasXEqualsY (const Clause*)");

  for (int i = c->length()-1; i >= 0; i--) {
    if (isXEqualsY((*c)[i],true)) {
      return true;
    }
  }
  return  false;
} // Property::hasXEqualsY (const Clause*)


/**
 * True is the atom has the form X=Y for X different from Y.
 * @since 22/05/2004 Manchester.
 * @since 27/05/2007 Frankfurt airport, changed to new datastructures
 */
bool Property::isXEqualsY (const Literal* lit,bool polarity)
{
  CALL("Property::isXEqualsY");

  if (! lit->isEquality()) {
    return false;
  }
  if (lit->isPositive()) {
    if (! polarity) {
      return false;
    }
  }
  else if (polarity) {
    return false;
  }

  // lit is an equality of the right polarity
  const TermList* ts1 = lit->args();
  if (! ts1->isVar()) {
    return false;
  }
  const TermList* ts2 = ts1->next();
  return ts2->isVar() &&
         ts1->var() != ts2->var();
} // Property::isXEqualsY(const Literals&)


/**
 * True if the subformula formula would have a literal X=Y
 * after clausification.
 *
 *
 * @warning Works correctly only with rectified formulas (closed or open)
 * @param f the formula
 * @param vc contains all universally quantified variables
 * @param polarity the polarity of this
 * @since 11/12/2004 Manchester, true and false added
 * @since 27/05/2007 flight Frankfurt-Lisbon, changed to new datastructures
 */
bool Property::hasXEqualsY (const Formula* f, MultiCounter& vc, int polarity)
{
  switch (f->connective()) {
  case LITERAL:
    return isXEqualsY(f->literal(),polarity);

  case AND:
  case OR:
    {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	if (hasXEqualsY(fs.next(),vc,polarity)) {
	  return true;
	}
      }
      return false;
    }

  case IMP:
    return hasXEqualsY(f->left(),vc,-polarity) ||
           hasXEqualsY(f->right(),vc,polarity);

  case IFF:
  case XOR:
    return hasXEqualsY(f->left(),vc,0) ||
           hasXEqualsY(f->right(),vc,0);

  case NOT:
    return hasXEqualsY(f->uarg(),vc,-polarity);

  case FORALL:
    // remember existentially quantified variables
    if (polarity == -1) {
      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
	vc.inc(vs.next());
      }
    }
    return hasXEqualsY(f->qarg(),vc,polarity);

  case EXISTS:
    // remember existentially quantified variables
    if (polarity == 1) {
      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
	vc.inc(vs.next());
      }
    }
    return hasXEqualsY(f->qarg(),vc,polarity);

  case ITE:
    return hasXEqualsY(f->condarg(),vc,0) ||
           hasXEqualsY(f->thenarg(),vc,polarity) ||
           hasXEqualsY(f->elsearg(),vc,polarity);

  case TERM_LET:
  case FORMULA_LET:
    //these two may introduce the X=Y literal but it would be too complicated to check for it
    return true;

  case TRUE:
  case FALSE:
    return false;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Property::hasXEqualsY (const Formula& f,...)


/**
 * Transforms the property to an SQL command asserting this
 * property to the Spider database. An example of a command is
 * "UPDATE problem SET property=0,category='NNE' WHERE name='TOP019-1';".
 *
 * @since 04/05/2005 Manchester
 */
string Property::toSpider (const string& problemName) const
{
  return (string)"UPDATE problem SET property="
    + Int::toString((int)_props)
    + ",category='"
    + categoryString()
    + "' WHERE name='"
    + problemName +
    + "';";
} // Property::toSpider

