/**
 * @file SMTParser.cpp
 * Implements class SMTParser
 *
 * @since 22/01/2009 Manchester
 */

#include <fstream>

#include "SMTLexer.hpp"
#include "SMTParser.hpp"

using namespace Lib;
using namespace Kernel;

namespace Shell {

/**
 * Initialise a SMT parser.
 * @since 22/01/2009 Manchester
 */
SMTParser::SMTParser (SMTLexer& lexer)
  : Parser(lexer)
{
}

/**
 * Build a benchmark
 * @since 24/01/2009 Lausanne
 */
SMTParser::Benchmark* SMTParser::benchmark()
{
  CALL("SMTParser::benchmark");

  consumeToken(TT_LPAR);
  readToken(TT_NAME);
  expectKeyword("benchmark");
  consumeToken();
  readToken(TT_NAME,"benchmark name expected");
  Benchmark* bench = new Benchmark(currentToken().text);
  consumeToken();
  readToken();
  while (currentToken().tag != TT_RPAR) {
    expectToken(TT_ATTRIBUTE);
    string attr = currentToken().text;
    if (attr == ":logic") {
      consumeToken();
      readToken();
      switch (currentToken().tag) {
      case TT_NAME:
	{
	  string logic = currentToken().text;
	  if (logic == "QF_RDL") {
	    bench->logic = QF_RDL;
	  }
	  else {
	    terminate((string)"unknown logic: '" + logic + "'");
	  }
	}
	consumeToken();
	readToken();
	break;
      default:
	terminate("logic name expected");
	return 0;
      }
    }
    else if (attr == ":assumption") {
      terminate("not implemented");
    }
    else if (attr == ":formula") {
      consumeToken();
      readToken();
      formula(&(bench->formula));
    }
    else if (attr == ":extrasorts") {
      terminate("not implemented");
    }
    else if (attr == ":extrafuns") {
      consumeToken();
      readToken(TT_LPAR);
      consumeToken();
      readToken();
      functions(&bench->functionDeclarations);
    }
    else if (attr == ":extrapreds") {
      consumeToken();
      readToken(TT_LPAR);
      consumeToken();
      readToken();
      predicates(&bench->predicateDeclarations);
    }
    else if (attr == ":notes") {
      terminate("not implemented");
    }
    else if (attr == ":status") {
      consumeToken();
      readToken();
      switch (currentToken().tag) {
      case TT_NAME:
	{
	  string stat = currentToken().text;
	  if (stat == "sat") {
	    bench->status = SAT;
	  }
	  else if (stat == "unsat") {
	    bench->status = UNSAT;
	  }
	  else if (stat == "unknown") {
	    bench->status = UNKNOWN;
	  }
	  else {
	    terminate("unknown status: '" + stat + "'");
	  }
	}
	consumeToken();
	readToken();
	break;
      default:
	terminate("status description expected");
      }
    }
    else { // annotation
      Annotation* ann = annotation();
      ann->next = bench->annotations;
      bench->annotations = ann;
    }
  }
  consumeToken(); // ')'
  readToken();
  return bench;
} // SMTParser::benchmark

/**
 * Read predicate declarations into @b dec. Stop after meeting ')'
 * after the last declaration. Consumes this ')' and read the next
 * token.
 * @since 27/01/2009 Manchester
 */
void SMTParser::predicates(PredicateDeclaration** decs)
{
  CALL("SMTParser::predicates");

  for (;;) {
    switch (currentToken().tag) {
    case TT_RPAR:
      consumeToken();
      readToken();
      return;
    case TT_LPAR:
      {
	consumeToken();
	readToken(TT_NAME,"predicate name expected");
	PredicateDeclaration* dec =
	  new PredicateDeclaration(currentToken().text);
	dec->next = *decs;
	*decs = dec;
	consumeToken();
	readToken(TT_RPAR,"complex predicate declarations not implemented");
	consumeToken();
	readToken();
      }
      break;
    default:
      terminate("predicate declaration expected");
    }
  }
} // SMTParser::predicates

/**
 * Read predicate declarations into @b dec. Stop after meeting ')'
 * after the last declaration. Consumes this ')' and read the next
 * token.
 * @since 27/01/2009 Manchester
 */
void SMTParser::functions(FunctionDeclaration** decs)
{
  CALL("SMTParser::functions");

  for (;;) {
    switch (currentToken().tag) {
    case TT_RPAR:
      consumeToken();
      readToken();
      return;
    case TT_LPAR:
      {
	consumeToken();
	readToken(TT_NAME,"function name expected");
	FunctionDeclaration* dec =
	  new FunctionDeclaration(currentToken().text);
	dec->next = *decs;
	*decs = dec;
	consumeToken();
	readToken(TT_NAME,"sort name expected");
	string sort = currentToken().text;
	if (sort == "Real") {
	  dec->sort = REAL;
	}
	else {
	  terminate("unknown sort: '" + sort + "'");
	}
	consumeToken();
	readToken(TT_RPAR,"complex function declarations not implemented");
	consumeToken();
	readToken();
      }
      break;
    default:
      terminate("function declaration expected");
    }
  }
} // SMTParser::functions

/**
 * Read and return an annotation. After reading the current token will be
 * the next one after the annotation
 * @pre the current token is an attribute
 * @since 27/01/2009 Manchester
 */
SMTParser::Annotation* SMTParser::annotation()
{
  CALL("SMTParser::annotation");
  ASS(currentToken().tag == TT_ATTRIBUTE);

  Annotation* ann = new Annotation();
  ann->next = 0;
  ann->attribute = currentToken().text;
  consumeToken();
  readToken();
  if (currentToken().tag != TT_USER) {
    ann->value = "";
    return ann;
  }
  ann->value = currentToken().text;
  consumeToken();
  readToken();
  return ann;
} // SMTParser::annotation

/**
 * Create a new benchmark with a given name.
 * @since 26/01/2009 Heathrow
 */
SMTParser::Benchmark::Benchmark(const string& nm)
  : name(nm),
    status(UNKNOWN),
    functionDeclarations(0),
    predicateDeclarations(0),
    annotations(0)
{}

/**
 * Create a new predicate declaration with a given name.
 * @since 27/01/2009 Manchester
 */
SMTParser::PredicateDeclaration::PredicateDeclaration(const string& nm)
  : name(nm),
    annotations(0),
    next(0)
{}

/**
 * Create a new function declaration with a given name.
 * @since 27/01/2009 Manchester
 */
SMTParser::FunctionDeclaration::FunctionDeclaration(const string& nm)
  : name(nm),
    annotations(0),
    next(0)
{}

/**
 * Read a formula and write it in @b form.
 * @since 27/01/2009 Manchester
 */
void SMTParser::formula(SMTParser::Formula** form)
{
  CALL("SMTParser::formula");

  consumeToken(TT_LPAR);
  readToken();
  switch (currentToken().tag) {
  case TT_NAME:
  case TT_ARITH:
    break;
  default:
    terminate("connective or predicate name expected");
  }
  string tokenText = currentToken().text;
  consumeToken();
  readToken();
  Connective con; 
  if (tokenText == "and") {
    con = AND;
  }
  else if (tokenText == "or") {
    con = OR;
  }
  else if (tokenText == "implies") {
    con = IMPLY;
  }
  else if (tokenText == "not") {
    con = NOT;
  }
  else if (tokenText == "xor") {
    con = XOR;
  }
  else if (tokenText == "iff") {
    con = IFF;
  }
  else if (tokenText == "if_then_else") {
    terminate("if-then-else formulas are not supported");
  }
  else { // atom
    Formula* atom = new Formula(ATOM);
    *form = atom;
    atom->atom = new Atom(tokenText);
    terms(&atom->atom->args);
    consumeToken(TT_RPAR);
    readToken();
    return;
  }
  *form = new Formula(con);
  formulas(&(*form)->args);
  
  consumeToken(TT_RPAR);
  readToken();
} // formula

/**
 * Read a list of formulas and write them in @b forms.
 * @since 27/01/2009 Manchester
 */
void SMTParser::formulas(SMTParser::Formula** forms)
{
  CALL("SMTParser::formulas");

  while (currentToken().tag != TT_RPAR) {
    formula(forms);
    forms = &(*forms)->next;
  }
} // formulas

/**
 * Read a list of terms and write them in @b ts.
 * @since 27/01/2009 Manchester
 */
void SMTParser::terms(SMTParser::Term** ts)
{
  CALL("SMTParser::terms");

  while (currentToken().tag != TT_RPAR &&
	 currentToken().tag != TT_ATTRIBUTE) {
    term(ts);
    ts = &(*ts)->next;
  }
} // terms

/**
 * Read a term and write them in @b t.
 * @since 28/01/2009 Gatwick
 */
void SMTParser::term(SMTParser::Term** t)
{
  CALL("SMTParser::term");

  switch (currentToken().tag) {
  case TT_NAME:
    *t = new Term(TERM_COMPLEX,currentToken().text);
    break;
  case TT_INTEGER:
    *t = new Term(TERM_INT,currentToken().text);
    break;
  case TT_REAL:
    ASS(false);
    *t = new Term(TERM_REAL,currentToken().text);
    break;
  case TT_LPAR:
    // complex term, consume the '(' token
    consumeToken();
    readToken();
    switch (currentToken().tag) {
    case TT_ARITH:
      *t = new Term(TERM_ARITH,currentToken().text);
      consumeToken();
      readToken();
      terms(&(*t)->args);
      break;
    case TT_NAME:
      *t = new Term(TERM_COMPLEX,currentToken().text);
      consumeToken();
      readToken();
      terms(&(*t)->args);
      break;
    case TT_INTEGER:
      *t = new Term(TERM_INT,currentToken().text);
      consumeToken();
      readToken();
      break;
    case TT_REAL:
      ASS(false);
      *t = new Term(TERM_REAL,currentToken().text);
      consumeToken();
      readToken();
      break;
    default:
      terminate("beginning of term expected");
    }
    // read annotations, if any
    while (currentToken().tag == TT_ATTRIBUTE) {
      Annotation* ann = annotation();
      ann->next = (*t)->annotations;
      (*t)->annotations->next = ann;
    }
    break;
  default:
    terminate("term expected");
  }
  consumeToken();
  readToken();
} // terms


}
