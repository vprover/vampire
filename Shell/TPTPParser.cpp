/**
 * @file TPTPParser.cpp
 * Implements class TPTPParser
 *
 * @since 14/07/2004 Turku
 */

#include <string.h>

#include <fstream>

#include "../Lib/List.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Environment.hpp"

#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Theory.hpp"

#include "../Shell/Statistics.hpp"

#include "../Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "TPTPLexer.hpp"
#include "TPTPParser.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Class that allows to create a list initially by pushing elements
 * at the end of it.
 * @since 10/05/2007 Manchester, updated from List::FIFO
 */
class TPTPParser::UnitStack {
public:
  /** constructor */
  inline explicit UnitStack()
    : _initial(0),
      _last(&_initial)
  {
  }

  /** add element at the end of the original list */
  inline void push(Unit* u)
  {
    UnitList* newList = new UnitList(u);
    *_last = newList;
    _last = reinterpret_cast<UnitList**>(&newList->tailReference());
  }

  /** Return the collected list */
  UnitList* list() { return _initial; }

  private:
  /** reference to the initial element */
  UnitList* _initial;
  /** last element */
  UnitList** _last;
}; // class UnitStack

class TPTPParser::LiteralStack
  : public Stack<Literal*>
{
public:
  /** Create an empty stack */
  inline LiteralStack()
    : Stack<Literal*>(64)
  {}
};

class TPTPParser::TermStack
  : public Stack<TermList>
{
public:
  /** Create an empty stack */
  inline TermStack()
    : Stack<TermList>(64)
  {}
};

/**
 * Initialise a TPTP parser.
 * @since 01/08/2004 Torrevieja
 */
TPTPParser::TPTPParser(TPTPLexer& lexer, int includeDepth)
  : Parser(lexer),
    _currentColor(COLOR_TRANSPARENT),
    _includeDepth(includeDepth),
    _namesLimited(false)
{
}


TPTPParser::TPTPParser(TPTPLexer& lexer, List<string>* allowedNames, int includeDepth)
  : Parser(lexer),
    _currentColor(COLOR_TRANSPARENT),
    _includeDepth(includeDepth),
    _namesLimited(true),
    _allowedNames(allowedNames)
{
}


/**
 * Parse a unit list.
 * @since 17/07/2004 Helsinki Airport
 * @since 02/05/2005 Manchester, changed to use stacks
 * @since 10/05/2007 Manchester, changed again
 */
UnitList* TPTPParser::units()
{
  CALL("TPTPParser::units()");

  UnitStack stack;
  units(stack);

  return stack.list();
} // TPTPParser::units

/**
 * Replace TT_NAME token type for keywords that are keywords
 * only when they appear at the top-level
 */
void TPTPParser::recognizeTopLevelTokens()
{
  Token& t=currentToken1();

  if(t.tag!=TT_NAME) {
    return;
  }

  const char* str=t.text.c_str();

  switch (str[0]) {
  case 'c':
    if (! strcmp(str,"cnf")) {
      t.tag=TT_CNF;
    }
    break;

  case 'f':
    if (! strcmp(str,"fof")) {
      t.tag=TT_INPUT_FORMULA;
    }
    break;

  case 'i':
    if (! strcmp(str,"input_formula")) {
      t.tag=TT_INPUT_FORMULA;
    }
    if (! strcmp(str,"input_clause")) {
      t.tag=TT_INPUT_CLAUSE;
    }
    if (! strcmp(str,"include")) {
      t.tag=TT_INCLUDE;
    }
    break;

  case 'v':
    if (! strcmp(str,"vampire")) {
      t.tag=TT_VAMPIRE;
    }
    break;

  default:
    break;
  }

}


/**
 * Parse units into a stack.
 * @since 02/05/2005 Manchester
 * @since 02/04/2008 Budapest, changed to read $true and $false in clauses
 */
void TPTPParser::units(UnitStack& stack)
{
  CALL("TPTPParser::units(UnitStack&)");

  for (;;) {
    if (env.timeLimitReached()) {
      return;
    }

    recognizeTopLevelTokens();

    switch (currentToken1().tag) {
    case TT_EOF:
      return;
    case TT_INCLUDE:
      consumeToken();
      include(stack);
      break;
    case TT_VAMPIRE:
      consumeToken();
      vampire();
      break;
    default:
      {
	Unit* u = unit();
// 	cout << u->toString() << "\n";
	if (u) {
	  stack.push(u);
	}
      }
      break;
    }
  }
} // TPTPParser::units

/**
 * Parse a unit. Return 0 if a clause with $true was read or a vampire() declaration discovered
 * otherwise the unit.
 * @since 17/07/2004 flight Helsinki-Stockholm
 * @since 02/05/2005 Manchester, changed to use stacks
 * @since 03/06/2007 Manchester, changed to new datastructures.
 * @since 02/04/2008 Budapest, changed to read $true and $false in clauses
 */
Unit* TPTPParser::unit()
{
  CALL("TPTPParser::unit");

  TokenType tag = currentToken1().tag;
  Unit* result;

  switch (tag) {
  case TT_INPUT_FORMULA:
  case TT_INPUT_CLAUSE:
  case TT_CNF:
    break;
  default:
    throw ParserException("either input_formula or input_clause expected",
			  currentToken());
  }
  consumeToken();

  consumeToken(TT_LPAR);
  string nm = name();

  bool allowedUnit=!_namesLimited || _allowedNames->member(nm);

  consumeToken(TT_COMMA);
  string tp = name();
  Unit::InputType it;
  _claim = 0;
  if (tp == "axiom") {
    it = Unit::AXIOM;
  }
  else if (tp == "definition") {
    it = Unit::AXIOM;
  }
  else if (tp == "conjecture") {
    it = Unit::CONJECTURE;
  }
  else if (tp == "negated_conjecture") {
    it = Unit::CONJECTURE;
  }
  else if (tp == "hypothesis") {
    it = Unit::ASSUMPTION;
  }
  else if (tp == "claim") {
    bool added;
    unsigned pred = env.signature->addPredicate(nm,0,added);
    if(!added) {
      USER_ERROR("Names of claims must be unique: "+nm);
    }
    env.signature->getPredicate(pred)->markCFName();
    Literal* a = new(0) Literal(pred,0,true,false);
    a = env.sharing->insert(a);
    _claim = new AtomicFormula(a);
    it = Unit::ASSUMPTION;
  }
  else if (tp == "lemma") {
    it = Unit::LEMMA;
  }
  else {
    throw ParserException("axiom, conjecture or hypothesis expected",
			  currentToken1());
  }

  consumeToken(TT_COMMA);

  switch (tag) {
  case TT_INPUT_FORMULA:
    {
      Formula* f = formula();
      if (it == Unit::CONJECTURE) {
	Formula::VarList* vs = f->freeVariables();
	if (vs->isEmpty()) {
	  f = new NegatedFormula(f);
	}
	else {
	  f = new NegatedFormula(new QuantifiedFormula(FORALL,vs,f));
	}
      }
      if (_claim) {
	Formula::VarList* vs = f->freeVariables();
	if (!vs->isEmpty()) {
	  f = new QuantifiedFormula(FORALL,vs,f);
	}
	f = new BinaryFormula(IFF,_claim,f);
      }
      result = new FormulaUnit(f,
			       new Inference( (it == Unit::CONJECTURE) ?
					       Inference::NEGATED_CONJECTURE :
					       Inference::INPUT),
			       it);
      if (_includeDepth) {
	result->markIncluded();
      }
      env.statistics->inputFormulas++;
    }
    break;

  case TT_INPUT_CLAUSE:
    result = clause(it);
    break;

  case TT_CNF:
    result = formulaClause(it);
    break;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
  consumeToken(TT_RPAR);
  consumeToken(TT_DOT);

  if(!allowedUnit) {
    return 0;
  }

  if (result) {
    result->setInheritedColor(_currentColor);
  }

  if(env.options->outputAxiomNames()) {
    s_axiomNames.insert(result->number(), nm);
  }

  return result;
} // TPTPParser::unit


/**
 * Parse a formula.
 * @since 17/07/2004 Stockholm airport
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Formula* TPTPParser::formula()
{
  CALL("TPTPParser::formula");

  Formula* f = iffFormula();
  Token& t = currentToken1();
  if (t.tag != TT_REVERSE_IMP) {
    return f;
  }
  // reverse implication
  consumeToken();
  return new BinaryFormula(IMP,formula(),f);
} // TPTPParser::formula


/**
 * Read and consume a single token of type TT_NAME.
 *
 * @since 26/07/2004 Torrevieja
 */
string TPTPParser::name ()
{
  CALL("TPTPParser::name");

  Token& token = currentToken1();

  if (token.tag != TT_NAME && token.tag != TT_INTEGER) {
    throw ParserException("name expected",
			  currentToken());
  }
  consumeToken();
  return token.text;
} // TPTPParser::name


/**
 * Read a clause
 * @since 10/05/2007 Manchester
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Clause* TPTPParser::clause(int inputType)
{
  CALL("TPTPParser::clause");

  consumeToken(TT_LBRA);
  LiteralStack lits;
  literals(lits);
  consumeToken(TT_RBRA);
  return createClause(lits,inputType);
} // TPTPParser::clause


/**
 * Read a clause in the formula syntax (as starting from in TPTP 3.0.1).
 * If true was read, return 0.
 * @since 02/05/2005 Manchester
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Clause* TPTPParser::formulaClause(int inputType)
{
  CALL("TPTPParser::formulaClause");

  bool par = false;
  if (currentToken1().tag == TT_LPAR) { // parentheses around the clause
    consumeToken();
    par = true;
  }
  _trueRead = false;
  LiteralStack lits;
  formulaLiterals(lits);
  if (par) {
    consumeToken(TT_RPAR);
  }
  return _trueRead ? 0 : createClause(lits,inputType);
} // TPTPParser::formulaClause


/**
 * Read a formula whose connective is different from the reverse
 * implication.
 * @since 20/05/2007 Manchester
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Formula* TPTPParser::iffFormula()
{
  CALL("TPTPParser::iffFormula");

  Formula* f = xorFormula();
  if (currentToken1().tag != TT_IFF) {
    return f;
  }

  consumeToken();
  return new BinaryFormula(IFF, f, xorFormula());
} // TPTPParser::xorFormula

/**
 * Read a formula whose connective is different from IFF.
 * @since 26/07/2004 Torrevieja
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Formula* TPTPParser::xorFormula ()
{
  CALL("TPTPParser::xorFormula");

  Formula* f = impFormula();
  if (currentToken1().tag != TT_XOR) {
    return f;
  }

  consumeToken();
  return new BinaryFormula(XOR,f,xorFormula());
} // TPTPParser::xorFormula


/**
 * Read a formula whose connective is different from IFF, XOR.
 * @since 26/07/2004 Torrevieja
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Formula* TPTPParser::impFormula ()
{
  CALL("TPTPParser::impFormula");

  Formula* f = orFormula();

  Token& t = currentToken1();
  if (t.tag !=  TT_IMP) {
    return f;
  }

  consumeToken();
  return new BinaryFormula(IMP,f,impFormula());
} // TPTPParser::impFormula


/**
 * Read a formula whose connective priority is at most OR.
 * @since 26/07/2004 Torrevieja
 * @since 03/06/2007 Manchester, changed to new datastructures.
 */
Formula* TPTPParser::orFormula ()
{
  CALL("TPTPParser::orFormula");

  Formula* lhs = andFormula();
  if (currentToken1().tag != TT_OR) {
    return lhs;
  }

  consumeToken();
  return makeJunction(OR,lhs,orFormula());
} // TPTPParser::orFormula


Formula* TPTPParser::makeJunction (int connective,Formula* lhs,Formula* rhs)
{
  Connective c = (Connective)connective;

  if (lhs->connective() == c) {
    FormulaList* largs = lhs->args();

    if (rhs->connective() == c) {
      FormulaList::concat(largs,rhs->args());
      delete static_cast<JunctionFormula*>(rhs);
      return lhs;
    }

    // only lhs has c as the main connective
    FormulaList::concat(largs,new FormulaList(rhs));
    return lhs;
  }

  // lhs' connective is not c
  if (rhs->connective() == c) {
    static_cast<JunctionFormula*>(rhs)->setArgs(new FormulaList(lhs,
								rhs->args()));
    return rhs;
  }

  // both connectives are not c
  return new JunctionFormula(c,
			     new FormulaList(lhs,
					     new FormulaList(rhs)));
} // Formula::makeJunction

/**
 * Read a formula whose connective priority is at most AND.
 * @since 26/07/2004 Torrevieja
 */
Formula* TPTPParser::andFormula ()
{
  CALL("TPTPParser::andFormula");

  Formula* f = simpleFormula();
  if (currentToken1().tag != TT_AND) {
    return f;
  }

  consumeToken();
  return makeJunction(AND,f,andFormula());
} // TPTPParser::andFormula

/**
 * Read a simple formula (quantified formula, negation,
 * formula in parentheses, true or false).
 *
 * @since 26/07/2004 Torrevieja
 * @since 11/12/2004 Manchester, true and false added
 */
Formula* TPTPParser::simpleFormula ()
{
  CALL("TPTPParser::simpleFormula");

  TokenType tt = currentToken1().tag;
  switch (tt) {
  case TT_NOT:
    consumeToken();
    return new NegatedFormula(simpleFormula());

  case TT_FORALL:
  case TT_EXISTS:
    {
      consumeToken();
      consumeToken(TT_LBRA);
      Formula::VarList* vs = varList();
      consumeToken(TT_RBRA);
      consumeToken(TT_COLON);
      Formula* f = simpleFormula();
      return new QuantifiedFormula(tt == TT_FORALL ? FORALL : EXISTS,vs,f);
    }

  case TT_LPAR:
    {
      consumeToken();
      Formula* f = formula();
      consumeToken(TT_RPAR);
      return f;
    }

  case TT_TRUE:
    consumeToken();
    return new Formula(true);

  case TT_FALSE:
    consumeToken();
    return new Formula(false);

  default: // atomic formula
    return new AtomicFormula(atom(true));
  }
} // TPTPParser::simpleFormula


/**
 * Read a non-empty list of variables in the quantifier prefix.
 * Variables are separated by commas.
 *
 * @since 26/07/2004 Torrevieja
 * @since 02/08/2004 Torrevieja, changed to use tail recursion
 */
List<int>* TPTPParser::varList()
{
  CALL("TPTPParser::varList");

  List<int>* result = List<int>::empty();
  List<int>::FIFO stack(result);

  for (;;) {
    Token& token = currentToken1();
    if (token.tag != TT_VAR) {
      throw ParserException("variable expected",token);
    }
    int v = var(token);
    stack.push(v);
    consumeToken();
    if (currentToken1().tag != TT_COMMA) {
      return result;
    }
    consumeToken();
  }
} // TPTPParser::varList

/**
 * Read a literal. A literal is an atom prefixed by ++ or --.
 * @since 26/07/2004 Torrevieja
 */
Literal* TPTPParser::literal()
{
  CALL("TPTPParser::literal");

  Token& token = currentToken1();
  switch (token.tag) {
  case TT_PP:
    consumeToken();
    return atom(true);

  case TT_MM:
    {
      consumeToken();
      return atom(false);
    }

  default:
    throw ParserException("either ++ or -- expected",token);
  }
} // TPTPParser::literal


/**
 * Read an atom. An atom can be either p, or p(t1,...,tn) or t1=t2.
 * @since 26/07/2004 Torrevieja
 * @since 30/09/2004 Manchester, integers and reals added
 * @since 29/12/2007 Manchester, polarity added
 */
Literal* TPTPParser::atom (bool polarity)
{
  CALL("TPTPParser::atom");

  Token& token = currentToken1();
  switch (token.tag) {
  case TT_NAME:
    {
      string functor = name();
      TermStack ts;
      args(ts);
      switch (currentToken1().tag) {
      case TT_NEQ:
	polarity = ! polarity;
	// no break is intended
      case TT_EQUAL:
	{
	  consumeToken();
	  Literal* l = Literal::equality(polarity);
	  TermList* args = l->args();
	  Term* t = makeTerm(functor,ts);
	  args->setTerm(t);
	  args = args->next();

	  int v;
	  t = term(v);
	  if (t) {
	    args->setTerm(t);
	  }
	  else {
	    args->makeVar(v);
	  }
	  return env.sharing->insert(l);
	}
      default:
	return makeAtom(functor,ts,polarity);
      }
    }

  case TT_REAL:
    throw ParserException("reading reals is not supported",token);
    
  case TT_INTEGER:
    {
      int v;
      Term* intTrm=term(v);
      ASS(intTrm);
      switch (currentToken1().tag) {
      case TT_NEQ:
	polarity = ! polarity;
	// no break is intended
      case TT_EQUAL:
	{
	  Literal* l = Literal::equality(polarity);
	  TermList* args = l->args();
	  args->setTerm(intTrm);
	  args = args->next();
	  consumeToken();
	  Term* t = term(v);
	  if (t) {
	    args->setTerm(t);
	  }
	  else {
	    args->makeVar(v);
	  }
	  return env.sharing->insert(l);
	}
      default:
	throw ParserException("= or != expected after term",token);
      }
    }
  case TT_VAR:
    {
      int v;
      term(v);
      switch (currentToken1().tag) {
      case TT_NEQ:
	polarity = ! polarity;
	// no break is intended
      case TT_EQUAL:
	{
	  Literal* l = Literal::equality(polarity);
	  TermList* args = l->args();
	  args->makeVar(v);
	  args = args->next();
	  consumeToken();
	  Term* t = term(v);
	  if (t) {
	    args->setTerm(t);
	  }
	  else {
	    args->makeVar(v);
	  }
	  return env.sharing->insert(l);
	}
      default:
	throw ParserException("= or != expected after term",token);
      }
    }

  default:
    throw ParserException("atom expected",token);
  }
} // TPTPParser::atom


/**
 * Read an term. A term can be a variable, a constant, or f(t1,...,tn).
 * If the term is a non-variable, return a pointer to the term. If it is
 * a variable, return 0 and save the variable number in v
 * @since 26/07/2004 Torrevieja
 * @since 30/09/2004 Manchester, integers and reals added
 * @since 16/05/2007 Manchester, rewritten for Prolog terms
 */
Term* TPTPParser::term(int& v)
{
  CALL("TPTPParser::term");

  Token& token = currentToken1();
  switch (token.tag) {
  case TT_NAME:
    {
      string functor = token.text;
      consumeToken();
      TermStack ts;
      args(ts);
      return makeTerm(functor,ts);
    }

  case TT_INTEGER:
    {
      string intStr = token.text;
      consumeToken();
      InterpretedType val;
      if(!Int::stringToInt(intStr, val)) {
        throw ParserException("unsupported integer value",token);
      }
      return theory->getRepresentation(val);
    }
  case TT_REAL:
    throw ParserException("reading reals is not supported",token);

  case TT_VAR:
    {
      v = var(token);
      consumeToken();
      return 0;
    }

  default:
    throw ParserException("term expected",token);
  }
} // TPTPParser::term


/**
 * Read arguments to an atom or term.
 *
 * @since 26/07/2004 Torrevieja
 * @since 16/05/2007 Manchester, changed to use Prolog terms
 */
void TPTPParser::args (TermStack& ts)
{
  CALL("TPTPParser::args");

  if (currentToken1().tag != TT_LPAR) {
    return;
  }
  consumeToken();

  for (;;) {
    int v;
    Term* t = term(v);
    TermList dummy;
    if (t) {
      dummy.setTerm(t);
    }
    else {
      dummy.makeVar(v);
    }
    ts.push(dummy);
    Token token = currentToken1();
    switch (token.tag) {
    case TT_COMMA:
      consumeToken();
      break;
    case TT_RPAR:
      consumeToken();
      return;
    default:
      throw ParserException("either ',' or ')' expected at the end of term",
			    token);
    }
  }
} // TPTPParser::args


/**
 * Read a non-empty list of literals separated by commas.
 *
 * @since 26/07/2004 Torrevieja
 * @since 16/05/2007 Manchester, changed to use Prolog terms
 * @since 02/04/2008 Budapest, changed to read $true and $false
 */
void TPTPParser::literals(LiteralStack& ls)
{
  CALL("TPTPParser::literals");

  for (;;) {
    Literal* lit = literal();
    ls.push(lit);
    switch (currentToken1().tag) {
    case TT_COMMA:
      consumeToken();
      break;
    default:
      return;
    }
  }
} // TPTPParser::literals


/**
 * Read a non-empty list of literals written as a formula.
 * Ignore any literals $false. If $true is read, set _trueRead
 * to true.
 *
 * @since 02/05/2005 Manchester
 * @since 16/05/2007 Manchester, changed to use Prolog terms
 * @since 02/04/2008 Budapest, changed to read $true and $false
 */
void TPTPParser::formulaLiterals(LiteralStack& ls)
{
  CALL("TPTPParser::formulaLiterals");

  for (;;) {
    Literal* lit = formulaLiteral();
    if (lit) {
      ls.push(lit);
    }
    switch (currentToken1().tag) {
    case TT_OR:
      consumeToken();
      break;
    default:
      return;
    }
  }
} // TPTPParser::formulaLiterals


/**
 * Read a literal in the formula syntax. If the literal contains
 * $true or $false then return 0. If $true or ~$false is read
 * set _trueRead to $true
 * @since 02/05/2005 Manchester
 * @since 16/05/2007 Manchester, changed to use Prolog terms
 * @since 02/04/2008 Budapest, changed to read $true and $false
 */
Literal* TPTPParser::formulaLiteral()
{
  CALL("TPTPParser::formulaLiteral");

  bool sign = true;
  Token& token = currentToken1();
  switch (token.tag) {
  case TT_NOT:
    consumeToken();
    sign = false;
    break;
  default:
    break;
  }

  token = currentToken1();
  switch (token.tag) {
  case TT_TRUE:
    if (sign) {
      _trueRead = true;
    }
    consumeToken();
    return 0;

  case TT_FALSE:
    if (! sign) {
      _trueRead = true;
    }
    consumeToken();
    return 0;

  default:
    break;
  }

  return atom(sign);
} // TPTPParser::formulaLiteral

// /**
//  * Translate a parser exception to its XML representation.
//  * @since 27/07/2004 Torrevieja
//  */
// XMLElement ParserException::toXML () const
// {
//   return XMLElement("parser_error",_message);
// } // ParserException::toXML


/**
 * Read the TPTP include command, execute it and save the resulting
 * units in the stack.
 *
 * @since 02/05/2005 Manchester
 */
void TPTPParser::include(UnitStack& stack)
{
  CALL("TPTPParser::include");

  consumeToken(TT_LPAR);
  Token& token = currentToken1();
  if (token.tag != TT_NAME) {
    throw ParserException("name expected",token);
  }
  string fileName(env.options->includeFileName(token.text));

  bool incLimited=false;
  List<string>* incAllowedNames;

  consumeToken();
  if(currentToken1().tag==TT_COMMA) {
    incLimited=true;
    incAllowedNames=0;

    consumeToken(TT_COMMA);
    consumeToken(TT_LBRA);
    for(;;) {
      string axName=currentToken1().text;
      if(!_namesLimited || _allowedNames->member(axName)) {
	List<string>::push(axName, incAllowedNames);
      }

      consumeToken();
      if(currentToken1().tag==TT_RBRA) {
	break;
      }
      consumeToken(TT_COMMA);
    }
    consumeToken(TT_RBRA);
  }
  consumeToken(TT_RPAR);
  consumeToken(TT_DOT);

  ifstream in(fileName.c_str());
  if (! in) {
    USER_ERROR((string)"cannot open file " + fileName);
  }
  TPTPLexer lexer(in);

  if(incLimited) {
    if(incAllowedNames) {
      TPTPParser parser(lexer, incAllowedNames, _includeDepth+1);
      parser.units(stack);
      incAllowedNames->destroy();
    }
  } else {
    TPTPParser parser(lexer, _includeDepth+1);
    parser.units(stack);
  }
} // TPTPParser::include

/**
 * Create a term from a functor and collected arguments.
 * @since 16/05/2007 Manchester
 */
Term* TPTPParser::makeTerm(const string& functor,TermStack& ts)
{
  CALL("TPTPParser::makeTerm");
  int arity = ts.length();

  unsigned fun = env.signature->addFunction(functor,arity);
  Term* t = new(arity) Term;
  t->makeSymbol(fun,arity);
  fillArgs(t,ts);
  return env.sharing->insert(t);
} // makeTerm

/**
 * Create a term from a functor and collected arguments.
 * @since 16/05/2007 Manchester
 */
Literal* TPTPParser::makeAtom(const string& functor,
			      TermStack& ts,
			      bool polarity)
{
  CALL("TPTPParser::makeAtom");
  int arity = ts.length();

  unsigned pred = env.signature->addPredicate(functor,arity);
  Literal* a = new(arity) Literal(pred,arity,polarity,false);
  fillArgs(a,ts);
  a = env.sharing->insert(a);
  return a;
} // makeAtom

/**
 * Fill arguments of a term t with values from the term stack ts.
 * @since 16/05/2007 Manchester
 */
void TPTPParser::fillArgs(Term* t,TermStack& ts)
{
  CALL("TPTPParser::fillArgs");

  int length = ts.length();
  TermList* args = t->args();
  for (int i = 0;i < length;i++) {
    *args = ts[i];
    args = args->next();
  }
} // TPTPParser::fillArgs

/**
 * Build a clause from a literal stack.
 * @since 18/05/2007 Manchester
 */
Clause* TPTPParser::createClause(LiteralStack& lits,int inputType)
{
  CALL("TPTPParser::createClause");

  unsigned length = lits.length();
  Clause* result = new(length) Clause(length,
				      (Unit::InputType)inputType,
				      new Inference(Inference::INPUT));
  if (_includeDepth) {
    result->markIncluded();
  }
  env.statistics->inputClauses++;
  for (int i=length-1;i >= 0;i--) {
    (*result)[i] = lits[i];
  }
  return result;
} // TPTPParser::createClause

/**
 * Read a Vampire-specific declaration
 * @since 25/08/2009 Redmond
 */
void TPTPParser::vampire()
{
  CALL("TPTPParser::vampire");

  consumeToken(TT_LPAR);
  string nm = name();
  if (nm == "option") { // vampire(option,age_weight_ratio,3)
    consumeToken(TT_COMMA);
    string opt = name();
    consumeToken(TT_COMMA);
    string val = name();
    env.options->set(opt,val);
  }
  else if (nm=="symbol") { // e.g. vampire(symbol,predicate,p,5,left).
    consumeToken(TT_COMMA);
    string kind = name();
    bool pred;
    if (kind == "predicate") {
      pred = true;
    }
    else if (kind == "function") {
      pred = false;
    }
    else {
      throw ParserException("either 'predicate' or 'function' expected",
			    currentToken1());
    }
    consumeToken(TT_COMMA);
    string symb = name();
    consumeToken(TT_COMMA);
    string art = name();
    unsigned arity;
    if (! Int::stringToUnsignedInt(art,arity)) {
      throw ParserException("a non-negative integer (denoting arity) expected",
			    currentToken1());
    }
    consumeToken(TT_COMMA);
    Color color;
    bool skip = false;
    string lr = name();
    if (lr == "left")
      color=COLOR_LEFT;
    else if (lr == "right")
      color=COLOR_RIGHT;
    else if (lr == "skip")
      skip = true;
    else {
      throw ParserException("'left', 'right' or 'skip' expected",
			    currentToken1());
    }
    env.colorUsed = true;
    Signature::Symbol* sym;
    if (pred)
      sym = env.signature->getPredicate(env.signature->addPredicate(symb,arity));
    else
      sym = env.signature->getFunction(env.signature->addFunction(symb,arity));

    if (skip)
      sym->markSkip();
    else
      sym->addColor(color);
  }
  else if (nm == "left_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_LEFT;
  }
  else if (nm == "right_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_RIGHT;
  }
  else if (nm == "end_formula") { // e.g. vampire(left_formula)
    _currentColor = COLOR_TRANSPARENT;
  }
  else if (nm == "interpreted_symbol") { // e.g. vampire(interpreted_symbol,+,integer_plus);
    consumeToken(TT_COMMA);
    string sname = name();
    consumeToken(TT_COMMA);
    string symb = name();
    if (symb == "integer_greater") {
      env.signature->registerInterpretedPredicate(sname,Theory::INT_GREATER);
    }
    else if (symb == "integer_greater_equal") {
      env.signature->registerInterpretedPredicate(sname,Theory::INT_GREATER_EQUAL);
    }
    else if (symb == "integer_less") {
      env.signature->registerInterpretedPredicate(sname,Theory::INT_LESS);
    }
    else if (symb == "integer_less_equal") {
      env.signature->registerInterpretedPredicate(sname,Theory::INT_LESS_EQUAL);
    }
    
    else if (symb == "greater") {
      env.signature->registerInterpretedPredicate(sname,Theory::GREATER);
    }
    else if (symb == "greater_equal") {
      env.signature->registerInterpretedPredicate(sname,Theory::GREATER_EQUAL);
    }
    else if (symb == "less") {
      env.signature->registerInterpretedPredicate(sname,Theory::LESS);
    }
    else if (symb == "less_equal") {
      env.signature->registerInterpretedPredicate(sname,Theory::LESS_EQUAL);
    }
    
    else if (symb == "successor") {
      env.signature->registerInterpretedFunction(sname,Theory::SUCCESSOR);
    }
    else if (symb == "integer_unary_minus") {
      env.signature->registerInterpretedFunction(sname,Theory::UNARY_MINUS);
    }
    else if (symb == "integer_plus") {
      env.signature->registerInterpretedFunction(sname,Theory::PLUS);
    }
    else if (symb == "integer_minus") {
      env.signature->registerInterpretedFunction(sname,Theory::MINUS);
    }
    else if (symb == "integer_product") {
      env.signature->registerInterpretedFunction(sname,Theory::MULTIPLY);
    }
    else if (symb == "integer_division") {
      env.signature->registerInterpretedFunction(sname,Theory::INT_DIVIDE);
    }
    else if (symb == "division") {
      env.signature->registerInterpretedFunction(sname,Theory::DIVIDE);
    }
    else {
      throw ParserException("unrecognised interpreted symbol",
                            currentToken());
    }
  }
  else {
    throw ParserException("unrecognised Vampire command",
			  currentToken1());
  }
  consumeToken(TT_RPAR);
  consumeToken(TT_DOT);
} // TPTPParser::vampire

