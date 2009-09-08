/**
 * @file SimplifyProver.cpp
 * Implements class SimplifyProver for working with files in the Simplify format
 *
 * @since 26/08/2009 Redmond
 */

#include "../Lib/Exception.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/Formula.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/FormulaVarIterator.hpp"

#include "SimplifyProver.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

#define TRACE 1

// This are the keywords not handled yet:
//     K_string,
//     K_number,
//     K_ID,
//     K_DEFPRED,
//     K_DEFPREDMAP,
//     K_DEFUN,
//     K_DEFINJ,
//     K_DEFCONSTRUCTOR,
//     K_DEFTUPLE,
//     K_DEFARRAY,
//     K_DEFWEAKARRAY,
//     K_DEFCOTUPLE,
//     K_DEFVALUE,
//     K_BG_POP,
//     K_LEMMA,
//     K_PROOF,
//     K_CHECK,
//     K_LET,
//     K_TERM,
//     K_ORDER,
//     K_LBLPOS,
//     K_LBLNEG,
//     K_LBL,
//     K_NOPATS,
//     K_MPAT,
//     K_PROMOTE,
//     K_EOS,
//     K_ITE,
//     K_EXPLIES,
//     K_PP,
//     K_DUMP_CTX,
//     K_DBG_VALID,
//     K_DBG_INVALID,
//     K_DBG_WAS_VALID,
//     K_DBG_WAS_INVALID,
//     K_ECHO,
//     K_invalid_string,
//     K_PROMPT_OFF,
//     K_PROMPT_ON,
//     K_EVALT,
//     K_EVALF,
//     K_EXIT,
//     K_ASYNC,
//     K_CANCEL,
//     K_MODEL,
//     K_STATS,
//     K_SLEEP


/**
 * Constructor for provers.
 * @since 27/08/2009 Redmond
 */
SimplifyProver::SimplifyProver()
  : _units(0), 
    _nextType(OTHER),
    _nextVar(0)
{
  addNumber("0");
  _zero = _numbers.top();
  addNumber("1");
  _one = _numbers.top();
}

/**
 * Destroy the prover info
 * @since 27/08/2009 Redmond
 */
SimplifyProver::~SimplifyProver()
{
  CALL("SimplifyProver::SimplifyProver");

  Map<string,SymbolInfo*>::Iterator it(_symbolInfo);
  while (it.hasNext()) {
    SymbolInfo* symInfo = it.next();
    DEALLOC_KNOWN(symInfo,sizeof(SymbolInfo) + sizeof(int)*(symInfo->arity - 1),"SimplifyProver::SymbolInfo");
  }
}

/**
 * Read all units from an expression
 * @since 26/08/2009 Redmond
 */
UnitList* SimplifyProver::units(const Expression* expr)
{
  CALL("SimplifyProver::units");

  List::Iterator it(expr->list);
  while (it.hasNext()) {
    Expression* exp = it.next();
    parse(exp);
  }
  return _units;
}

/**
 * Read units from a top-level expression
 * @since 26/08/2009 Redmond
 */
void SimplifyProver::parse(const Expression* expr)
{
  CALL("SimplifyProver::topLevel");

  if (expr->tag == LispParser::ATOM) {
    switch (keyword(expr->str))
      {
      case K_DBG_WAS_VALID:
	// ignore these commands
	return;
      default:
	error(expr->str + " not implemented\n");
      }
    return;
  }

  List* list = expr->list;
  Expression* head = list->head();
  if (head->tag == LispParser::LIST) error("This kind of top-level expression is not implemented\n" + expr->toString());
  switch (keyword(head->str)) {
  case K_DEFTYPE:
    defType(list,expr);
    return;
  case K_DEFOP:
    defOp(list,expr);
    return;
  case K_BG_PUSH:
    bgPush(list);
    return;

  case K_SETPARAMETER: // ignore these parameters
    return;
  default:
    error("Not implemented: " + expr->toString());
  }
} // topLevel

/**
 * Return the keyword tag corresponding to the string @b str (K_NONE if not a keyword)
 * @since 26/08/2009 Redmond
 */
SimplifyProver::Keyword SimplifyProver::keyword(const string& str)
{
  CALL("SimplifyProver::keyword");

  if (str == "") {
    return K_NONE;
  }

  switch (str.at(0)) {
  case 'n':
    if (str == "number") return K_number;
    break;
  case 's':
    if (str == "string") return K_string;
    break;
  case 'A':
    if (str == "AND") return K_AND;
    if (str == "ASYNC") return K_ASYNC;
    break;
  case 'B':
    if (str == "BG_PUSH") return K_BG_PUSH;
    if (str == "BG_POP") return K_BG_POP;
    break;
  case 'C':
    if (str == "CHECK*") return K_CHECK;
    if (str == "CANCEL") return K_CANCEL;
    break;
  case 'D':
    if (str == "DEFPRED") return K_DEFPRED;
    if (str == "DEFUN") return K_DEFUN;
    if (str == "DEFCONSTRUCTOR") return K_DEFCONSTRUCTOR;
    if (str == "DEFINJ") return K_DEFINJ;
    if (str == "DEFTUPLE") return K_DEFTUPLE;
    if (str == "DEFARRAY") return K_DEFARRAY;
    if (str == "DEFWEAKARRAY") return K_DEFWEAKARRAY;
    if (str == "DEFCOTUPLE") return K_DEFCOTUPLE;
    if (str == "DEFVALUE") return K_DEFVALUE;
    if (str == "DEFOP") return K_DEFOP;
    if (str == "DEFTYPE") return K_DEFTYPE;
    if (str == "DISTINCT") return K_DISTINCT;
    if (str == "DUMP_CTX") return K_DUMP_CTX;
    if (str == "DBG_VALID") return K_DBG_VALID;
    if (str == "DBG_INVALID") return K_DBG_INVALID;
    if (str == "DBG_WAS_VALID") return K_DBG_WAS_VALID;
    break;
  case 'E':
    if (str == "EXISTS") return K_EXISTS;
    if (str == "EOS") return K_EOS;
    if (str == "EXPLIES") return K_EXPLIES;
    if (str == "EQ") return K_EQ;
    if (str == "ECHO") return K_ECHO;
    if (str == "EVALT") return K_EVALT;
    if (str == "EVALF") return K_EVALF;
    if (str == "EXIT") return K_EXIT;
    break;
  case 'F':
    if (str == "FORALL") return K_FORALL;
    if (str == "FORMULA") return K_FORMULA;
    if (str == "FALSE") return K_FALSE;
    break;
  case 'I':
    if (str == "ID") return K_ID;
    if (str == "IMPLIES") return K_IMPLIES;
    if (str == "IFF") return K_IFF;
    if (str == "ITE") return K_ITE;
    break;
  case 'L':
    if (str == "LEMMA") return K_LEMMA;
    if (str == "LET") return K_LET;
    if (str == "LBLPOS") return K_LBLPOS;
    if (str == "LBLNEG") return K_LBLNEG;
    if (str == "LBL") return K_LBL;
    break;
  case 'M':
    if (str == "MPAT") return K_MPAT;
    if (str == "MODEL") return K_MODEL;
    break;
  case 'N':
    if (str == "NOPATS") return K_NOPATS;
    if (str == "NOT") return K_NOT;
    if (str == "NEQ") return K_NEQ;
    break;
  case 'O':
    if (str == "ORDER") return K_ORDER;
    if (str == "OR") return K_OR;
    break;
  case 'P':
    if (str == "PROOF") return K_PROOF;
    if (str == "PATS") return K_PATS;
    if (str == "PROMOTE") return K_PROMOTE;
    if (str == "PP") return K_PP;
    if (str == "PROMPT_OFF") return K_PROMPT_OFF;
    if (str == "PROMPT_ON") return K_PROMPT_ON;
    break;
  case 'Q':
    if (str == "QID") return K_QID;
    break;
  case 'S':
    if (str == "SETPARAMETER") return K_SETPARAMETER;
    if (str == "SKOLEMID") return K_SKOLEMID;
    if (str == "STATS") return K_STATS;
    if (str == "SLEEP") return K_SLEEP;
    break;
  case 'T':
    if (str == "TERM") return K_TERM;
    if (str == "TRUE") return K_TRUE;
    break;
  case 'W':
    if (str == "WEIGHT") return K_WEIGHT;
    break;
  case ':':
    if (str == ":BUILTIN") return K_BUILTIN;
    if (str == ":TYPE") return K_TYPE;
    break;
  case '<':
    if (str == "<invalid-string>") return K_invalid_string;
    break;
  default:
    break;
  }
  return K_NONE;
} // keyword

/** Create a typoinfo structure and allocate the argTypes array */
SimplifyProver::SymbolInfo::SymbolInfo(int ar)
  : arity(ar)
{
}

/** allocate a new SymbolInfo structure */
void* SimplifyProver::SymbolInfo::operator new(size_t size, int arity)
{
  return ALLOC_KNOWN(size + sizeof(int)*(arity-1),"SimplifyProver::SymbolInfo");
}

/** Bind a variable name to the variable number */
int SimplifyProver::bindVar(const string& varName)
{
  CALL("SimplifyProver::bindVar");

  IntList* bindings;
  if (! _variables.find(varName,bindings)) {
    bindings = 0;
  }
  bindings = new IntList(_nextVar,bindings);
  _variables.replaceOrInsert(varName,bindings);
  return _nextVar++;
} // bindVar

/** Unbind a variable name */
void SimplifyProver::unbindVar(const string& varName)
{
  CALL("SimplifyProver::unbindVar");

  IntList* bindings;
  _variables.find(varName,bindings);
  IntList* tl = bindings->tail();
  delete bindings;
  bindings = tl;
  _variables.replaceOrInsert(varName,bindings);
} // bindVar

/**
 * Parse a formula declaration
 * @since 31/08/2009, Redmond
 */
void SimplifyProver::parse()
{
  CALL("SimplifyProver::formula");

  while (! _commands.isEmpty()) {
    Command cmd = _commands.pop();
    switch (cmd) {
    case PARSE_FORMULA:
      parseFormula();
      break;
    case PARSE_TERM:
      parseTerm();
      break;
    case BUILD_TERM:
      buildTerm();
      break;
    case BUILD_ATOM:
      buildAtom();
      break;
    case BUILD_BINARY_FORMULA:
      buildBinaryFormula();
      break;
    case BUILD_JUNCTION_FORMULA:
      buildJunctionFormula();
      break;
    case BUILD_QUANTIFIED_FORMULA:
      buildQuantifiedFormula();
      break;
    case BUILD_NEGATED_FORMULA:
      buildNegatedFormula();
      break;
    case BUILD_EQUALITY:
      buildEquality();
      break;
    case BUILD_DISTINCT:
      buildDistinct();
      break;
    default:
      error((string)"Cannot handle command "+Int::toString(cmd));
    }
  }
  return;
} // formula()

/**
 * Report a formula parsing error and raise an exception.
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::formulaError(const Expression* expr)
{
  CALL("SimplifyProver::formulaError");
  error((string)"Formula " + expr->toString() + " cannot be parsed");
} // formulaError

/**
 * Report a term parsing error and raise an exception.
 * @since 31/08/2009, Redmond
 */
void SimplifyProver::termError(const Expression* expr)
{
  CALL("SimplifyProver::termError");
  error((string)"Term " + expr->toString() + " cannot be parsed");
} // termError

/**
 * Report and error and raise an exception.
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::error(const string& str)
{
  CALL("SimplifyProver::error");
  cerr << str << '\n';
  throw Exception(str);
} // error

/**
 * Parse a formula from an expression
 * The resulting formula will be pushed on the stack _parsed
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseFormula()
{
  CALL("SimplifyProver::parseFormula");

  const Expression* expr = (const Expression*)_saved.pop();
  Context context = (Context)_isaved.pop();
#if TRACE
  cout << "Formula: " << expr->toString() << '\n';
#endif
  if (expr->tag == LispParser::LIST) {
    List* lst = expr->list;
    if (lst->length() == 0) formulaError(expr);
    string head = lst->head()->str;

    switch (keyword(head)) {
    case K_AND:
      parseJunctionFormula(lst,expr,AND,context);
      return;
    case K_OR:
      parseJunctionFormula(lst,expr,OR,context);
      return;
    case K_FORALL:
      parseQuantifiedFormula(lst,expr,FORALL,context);
      return;
    case K_EXISTS:
      parseQuantifiedFormula(lst,expr,EXISTS,context);
      return;
    case K_IMPLIES:
      parseBinaryFormula(lst->tail(),expr,IMP,context);
      return;
    case K_IFF:
      parseBinaryFormula(lst->tail(),expr,IFF,context);
      return;
    case K_NOT:
      parseNegatedFormula(lst->tail(),expr,context);
      return;
    case K_NONE: // literal
      parseAtom(lst,expr,context);
      return;
    case K_EQ:
      parseEquality(lst,expr,context,true);
      return;
    case K_NEQ:
      parseEquality(lst,expr,context,false);
      return;
    case K_DISTINCT:
      parseDistinct(lst,expr,context);
      return;
    default:
      formulaError(expr);
    }
    return;
  }

  // not list, an atom
  switch (keyword(expr->str)) {
  case K_NONE:
    parseAtom(expr,context);
    return;
  case K_TRUE:
    _built.push(new Formula(true));
    return;
  case K_FALSE:
    _built.push(new Formula(false));
    return;
  default:
    formulaError(expr);
  }
} // parseFormula

/**
 * Parse a quantified formula from a list of expressions
 * The resulting formula will be pushed on the stack _parsed
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseQuantifiedFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseQuantifiedFormula");

  Stack<int> booleanVars;
  lst = lst->tail();
  int len = lst->length();
  if (len < 2) formulaError(expr);
  // parsing variable sequence
  if (lst->head()->tag != LispParser::LIST) formulaError(expr);
  List* vars = lst->head()->list;
  for (List* vs = vars;vs;vs = vs->tail()) {
    if (vs->head()->tag == LispParser::LIST) formulaError(expr);
  }
  IntList* qvars = 0;
  IntList** qvarsTailPtr = &qvars;
  _saved.push(vars);
  while (vars) {
    // bind a new variable and add it to qvars
    string vname = vars->head()->str;
    if (keyword(vname) != K_NONE) formulaError(expr);
    int varNumber = bindVar(vname);
    IntList* lvar = new IntList(varNumber);
    *qvarsTailPtr = lvar;
    qvarsTailPtr = lvar->tailPtr();
	  
    vars = vars->tail();
    if (! vars || keyword(vars->head()->str) != K_TYPE) {
      continue;
    }
    // the type of the variable id declared
    vars = vars->tail();
    if (! vars) formulaError(expr);
    Type tp;
    if (! _types.find(vars->head()->str,tp)) formulaError(expr);
    if (tp == BIT_BOOL) {
      booleanVars.push(varNumber);
    }
    vars = vars->tail();
  }
  _built.push(qvars);
  // if there are boolean variables in the quantifier, then the formula (Q x)F should be changed
  // into (Q x)(prefix -> F), where prefix is x=0 \/ x=1
  _isaved.push(booleanVars.length());
  while (! booleanVars.isEmpty()) {
    TermList x(booleanVars.pop(),false);
    Formula* l = new AtomicFormula(Literal::createEquality(true,x,_zero));
    Formula* r = new AtomicFormula(Literal::createEquality(true,x,_one));
    _built.push(new JunctionFormula(OR,
				    new FormulaList(new Formula(l),
						    new FormulaList(r))));
  }

  lst = lst->tail();
  const Expression* ex = lst->head();
  while (lst->tail()) {
    if (ex->tag != LispParser::LIST) formulaError(expr);
    switch (keyword(ex->list->head()->str)) {
    case K_QID: // ignore QID command
    case K_PATS: // ignore PATS command
    case K_SKOLEMID: // ignore SKOLEMID command
    case K_WEIGHT: // ignore WEIGHT command
      lst = lst->tail();
      ex = lst->head();
      break;
    default:
      formulaError(expr);
    }
  }
  _isaved.push((int)c);
  _isaved.push((int)context);
  _commands.push(BUILD_QUANTIFIED_FORMULA);
  _saved.push(ex);
  _isaved.push(CN_FORMULA);
  _commands.push(PARSE_FORMULA);
} // SimplifyProver::parseQuantifiedFormula

/**
 * Parse a formula with a binary connective from a list of expressions
 * The resulting formula will be pushed on the stack _parsed
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseBinaryFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseBinaryFormula");

  if (lst->length()!=2) formulaError(expr);
  _isaved.push(c);
  _isaved.push(context);
  _commands.push(BUILD_BINARY_FORMULA);

  _isaved.push(CN_FORMULA);
  _saved.push(lst->head());
  _commands.push(PARSE_FORMULA);

  lst=lst->tail();
  _isaved.push(CN_FORMULA);
  _saved.push(lst->head());
  _commands.push(PARSE_FORMULA);
} // SimplifyProver::parseBinaryFormula

/**
 * Parse a formula with a binary connective from a list of expressions
 * The resulting formula will be pushed on the stack _parsed
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseJunctionFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseJunctionFormula");

  if (lst->length() <= 2) formulaError(expr);
  lst = lst->tail();
  _isaved.push(lst->length());
  _isaved.push((int)c);
  _isaved.push(context);
  _commands.push(BUILD_JUNCTION_FORMULA);
  List::Iterator lit(lst);
  while (lit.hasNext()) {
    _saved.push(lit.next());
    _isaved.push(CN_FORMULA);
    _commands.push(PARSE_FORMULA);
  }
} // SimplifyProver::parseJunctionFormula

/**
 * Parse an atom from a list of expressions
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseAtom(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseAtom");

  if (lst->head()->tag == LispParser::LIST) formulaError(expr);
  string symb = lst->head()->str;
  int arity = lst->length() - 1;
  SymbolInfo* sinfo;
  if (!_symbolInfo.find(symb,sinfo)) {
    sinfo = builtInPredicate(symb,arity);
    if (! sinfo) error((string)"predicate symbol " + symb + " not previously defined");
  }
  _saved.push(sinfo);
  if (sinfo->arity != arity) error((string)"predicate symbol " + symb + "is used with an arity different from declared");
  if (sinfo->returnType != BIT_BOOL) error((string)"symbol " + symb + "is used both as a function and as a predicate");
  _commands.push(BUILD_ATOM);
  _isaved.push(context);
  List::Iterator lit(lst->tail());
  Type* types = (Type*)(sinfo->argTypes);
  while (lit.hasNext()) {
    _saved.push(lit.next());
    if (*types == BIT_BOOL) {
      _isaved.push(CN_ARGUMENT);
      _commands.push(PARSE_FORMULA);
    }
    else {
      _commands.push(PARSE_TERM);
    }
    types++;
  }
} // parseAtom

/**
 * Parse an atom from an atomic formula expressions
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseAtom(const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseAtom");

  string symb = expr->str;
  SymbolInfo* sinfo;
  if (!_symbolInfo.find(symb,sinfo)) {
    sinfo = builtInPredicate(symb,0);
    if (! sinfo) error((string)"predicate symbol " + symb + " not previously defined");
  }
  if (sinfo->arity != 0) error((string)"predicate symbol " + symb + "is used with an arity different from declared");
  if (sinfo->returnType != BIT_BOOL) error((string)"symbol " + symb + "is used both as a function and as a predicate");

  Literal* lit = Literal::create(sinfo->number,0,true,false,0);
  processFormula(new AtomicFormula(lit),context);
} // parseAtom

/**
 * Parse a DISTINCT formula
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::parseDistinct(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseDistinct");

  lst = lst->tail();
  int length = lst->length();
  if (length < 2) {
    return;
  }
  _isaved.push(length);
  _isaved.push(context);
  _commands.push(BUILD_DISTINCT);
  List::Iterator lit(lst);
  while (lit.hasNext()) {
    _saved.push(lit.next());
    _commands.push(PARSE_TERM);
  }
} // parseDistinct

/**
 * Parse an equality atom
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::parseEquality(const List* lst,const Expression* expr,Context context,bool polarity)
{
  CALL("SimplifyProver::parseEquality");

  if (lst->length() != 3) formulaError(expr);
  _isaved.push(polarity);
  _isaved.push(context);
  _commands.push(BUILD_EQUALITY);
  lst=lst->tail();
  _saved.push(lst->head());
  _commands.push(PARSE_TERM);
  lst=lst->tail();
  _saved.push(lst->head());
  _commands.push(PARSE_TERM);
} // parseEquality

/**
 * True if symb is a built-in predicate. Built-in predicates do not
 * have to be declared in advance but they can be used.
 * @since 29/08/2009, Redmond
 */
SimplifyProver::SymbolInfo* SimplifyProver::builtInPredicate(const string& symb,int arity)
{
  CALL("SimplifyProver::builtInPredicate");

  bool isEquality = false;
  if (symb == ">=") {
    if (arity != 2) return 0;
  }
  else if (symb == "<=") {
    if (arity != 2) return 0;
  }
  else if (symb == "EQ") {
    if (arity != 2) return 0;
    isEquality = true;
  }

  SymbolInfo* sinfo = new(arity) SymbolInfo(arity);
  sinfo->returnType = BIT_BOOL;
  sinfo->number = isEquality ? 0 : env.signature->addPredicate(symb,arity);
  for (int i = 0;i < arity;i++) {
    sinfo->argTypes[i] = BIT_INT;
  }
  _symbolInfo.insert(symb,sinfo);
  return sinfo;
} // SimplifyProver::builtInPredicate

/**
 * True if symb is a built-in function. Built-in functions do not
 * have to be declared in advance but they can be used.
 * @since 31/08/2009, Redmond
 */
SimplifyProver::SymbolInfo* SimplifyProver::builtInFunction(const string& symb,int arity)
{
  CALL("SimplifyProver::builtInFunction");

  if (symb == "+") {
    if (arity != 2) return 0;
  }
  else if (symb == "-") {
    if (arity != 2) return 0;
  }
//   else if (arity != 0) {
//     return 0;
//   }
//   else {
//     for (int i = symb.length()-1;i >= 0;i--) {
//       char s = symb.at(i);
//       if (s < '0' || s > '9') return 0;
//     }
//     // it is an integer
//   }
  SymbolInfo* sinfo = new(arity) SymbolInfo(arity);
  sinfo->returnType = BIT_INT;
  sinfo->number = env.signature->addFunction(symb,arity);
  for (int i = 0;i < arity;i++) {
    sinfo->argTypes[i] = BIT_INT;
  }

  _symbolInfo.insert(symb,sinfo);
  return sinfo;
} // SimplifyProver::builtInFunction

/**
 * Parse a term from a list of expressions
 * @since 29/08/2009, Redmond
 */
void SimplifyProver::parseTerm()
{
  CALL("SimplifyProver::parseTerm");

  const Expression* expr = (const Expression*)_saved.pop();
#if TRACE
  cout << "Term: " << expr->toString() << '\n';
#endif
  if (expr->tag == LispParser::ATOM) {
    string symb = expr->str;
    IntList* bindings;
    if (_variables.find(symb,bindings)) {
      TermList ts(bindings->head(),false);
      _tsaved.push(ts);
#if TRACE
  cout << "TERM: " << ts.toString() << '\n';
#endif
      return;
    }
    SymbolInfo* sinfo;
    if (!_symbolInfo.find(symb,sinfo)) {
      sinfo = builtInFunction(symb,0);
      if (! sinfo) error((string)"function symbol " + symb + " not previously defined");
    }
    if (sinfo->arity != 0) error((string)"function symbol " + symb + "is used with an arity different from declared");
    if (sinfo->returnType == BIT_BOOL) error((string)"symbol " + symb + "is used both as a constant and as a predicate");
    TermList ts;
    Term* t = Term::create(sinfo->number,0,0);
    ts.setTerm(t);
    _tsaved.push(ts);
#if TRACE
  cout << "TERM: " << ts.toString() << '\n';
#endif
    return;
  }

  List* lst = expr->list;
  if (lst->head()->tag == LispParser::LIST) termError(expr);
  string symb = lst->head()->str;
  int arity = lst->length() - 1;
  SymbolInfo* sinfo;
  if (!_symbolInfo.find(symb,sinfo)) {
    sinfo = builtInFunction(symb,arity);
    if (! sinfo) error((string)"function symbol " + symb + " not previously defined");
  }
  _saved.push(sinfo);
  if (sinfo->arity != arity) error((string)"function symbol " + symb + "is used with an arity different from declared");
  if (sinfo->returnType == BIT_BOOL) error((string)"symbol " + symb + "is used both as a function and as a predicate");
  _commands.push(BUILD_TERM);
  List::Iterator lit(lst->tail());
  Type* types = (Type*)(sinfo->argTypes);
  while (lit.hasNext()) {
    _saved.push(lit.next());
    if (*types == BIT_BOOL) {
      _isaved.push(CN_ARGUMENT);
      _commands.push(PARSE_FORMULA);
    }
    else {
      _commands.push(PARSE_TERM);
    }
    types++;
  }
} // parseTerm

/**
 * Parse a DEFTYPE declaration
 * @since 31/08/2009, Redmond
 */
void SimplifyProver::defType(const List* list,const Expression* expr)
{
  CALL("SimplifyProver::defType");

  int length = list->length();
  if (length == 0) {
  err:
    error((string)"Bad DEFTYPE declaration " + expr->toString());
  }
  List* l1 = list->tail();
  Expression* h1 = l1->head();
  if (h1->tag == LispParser::LIST) goto err;
  string typeName = h1->str;
  if (keyword(typeName) != K_NONE) goto err;
      
  if (length == 2) {
    _types.insert(typeName,(Type)_nextType);
    _nextType++;
    return;
  }
  if (length != 4) goto err;
  List* l2 = l1->tail();
  if (l2->head()->tag == LispParser::LIST) goto err;
  if (keyword(l2->head()->str) != K_BUILTIN) goto err;
  List* l3 = l2->tail();
  if (l3->head()->tag == LispParser::LIST) goto err;
  Type tp;
  if (l3->head()->str == "Int") {
    tp = BIT_INT;
  }
  else if (l3->head()->str == "bool") {
    tp = BIT_BOOL;
  }
  else {
    goto err;
  }
  _types.insert(typeName,tp);
} // SimplifyProver::defType

/**
 * Parse a DEFOP declaration
 * @since 31/08/2009, Redmond
 */
void SimplifyProver::defOp(const List* list,const Expression* expr)
{
  CALL("SimplifyProver::defOp");

  int length = list->length();
  if (length < 3) {
  err:
    error((string)"Bad DEFOP declaration " + expr->toString());
  }
  List* l1 = list->tail();
  Expression* h1 = l1->head();
  if (h1->tag == LispParser::LIST) goto err;
  string symb = h1->str;
  if (keyword(symb) != K_NONE) goto err;
  SymbolInfo* symInfo = new(length-3) SymbolInfo(length-3);
  for (int argNo = 0;argNo<length-3;argNo++) {
    l1 = l1->tail();
    h1 = l1->head();
    if (h1->tag == LispParser::LIST) goto err;
    string typeName = h1->str;
    if (keyword(typeName) != K_NONE) goto err;
    Type tp;
    if (! _types.find(typeName,tp)) error((string)"Type " + typeName + " not declared in " + expr->toString());
    if (tp == BIT_BOOL) {
      _hasBooleanArgs.insert(symb);
    }
    symInfo->argTypes[argNo] = tp;
  }
  l1 = l1->tail();
  ASS(! l1->tail());
  h1 = l1->head();
  if (h1->tag == LispParser::LIST) goto err;
  string typeName = h1->str;
  if (keyword(typeName) != K_NONE) goto err;
  Type tp;
  if (! _types.find(typeName,tp)) error((string)"Type " + typeName + " not declared in " + expr->toString());
  symInfo->returnType = tp;
  _symbolInfo.insert(symb,symInfo);
  // Insert the symbol to the signature
  if (tp == BIT_BOOL) {
    symInfo->number = env.signature->addPredicate(symb,length-3);
  }
  else {
    symInfo->number = env.signature->addFunction(symb,length-3);
  }
} // SimplifyProver::defOp

/**
 * Parse a BG_PUSH command
 * @since 31/08/2009, Redmond
 */
void SimplifyProver::bgPush(const List* list)
{
  CALL("SimplifyProver::bgPush");

  for (List* l1 = list->tail();l1;l1 = l1->tail()) {
    _saved.push(l1->head());
    _commands.push(PARSE_FORMULA);
    _isaved.push(CN_TOP_LEVEL);
  }
  parse();
} // bgPush

/**
 * Build a parsed term
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildTerm()
{
  CALL("SimplifyProver::buildTerm");
  static DArray<TermList> args;

  const SymbolInfo* sinfo = (SymbolInfo*)_saved.pop();
  int arity = sinfo->arity;
  args.ensure(arity);
  for (int i = 0;i < arity;i++) {
    args[i] = _tsaved.pop();
  }
  TermList ts(Term::create(sinfo->number,arity,args.array()));
#if TRACE
  cout << "TERM: " << ts.toString() << '\n';
#endif
  _tsaved.push(ts);
} // buildTerm

/**
 * Build a parsed atom
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildAtom()
{
  CALL("SimplifyProver::buildAtom");
  static DArray<TermList> args;

  const SymbolInfo* sinfo = (SymbolInfo*)_saved.pop();
  Context context = (Context)_isaved.pop();
  int arity = sinfo->arity;
  args.ensure(arity);
  for (int i = 0;i < arity;i++) {
    args[i] = _tsaved.pop();
  }
  Literal* lit = sinfo->number == 0 // equality
                 ? Literal::createEquality(true,args[0],args[1])
                 : Literal::create(sinfo->number,arity,true,false,args.array());
  processFormula(new AtomicFormula(lit),context);
} // buildAtom

/**
 * Build a binary formula
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildBinaryFormula()
{
  CALL("SimplifyProver::buildBinaryFormula");

  Context context = (Context)_isaved.pop();
  Connective con = (Connective)_isaved.pop();

  Formula* r = (Formula*)_built.pop();
  Formula* l = (Formula*)_built.pop();
  processFormula(new BinaryFormula(con,l,r),context);
} // buildBinaryFormula

/**
 * Build a negated formula
 * @since 04/09/2009, Redmond
 */
void SimplifyProver::buildNegatedFormula()
{
  CALL("SimplifyProver::buildNegatedFormula");

  Context context = (Context)_isaved.pop();
  Formula* f = (Formula*)_built.pop();
  processFormula(new NegatedFormula(f),context);
} // buildNegatedFormula

/**
 * Build a conjunction or a disjunction
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildJunctionFormula()
{
  CALL("SimplifyProver::buildJunctionFormula");

  FormulaList* fs = 0;

  Context context = (Context)_isaved.pop();
  Connective con = (Connective)_isaved.pop();
  for (int i = _isaved.pop();i > 0;i--) { // i=length of the junction
    Formula* f = (Formula*)_built.pop();
    fs = new FormulaList(f,fs);
  }
  processFormula(new JunctionFormula(con,fs),context);
} // buildJunctionFormula

/**
 * Build a quantified formula
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildQuantifiedFormula()
{
  CALL("SimplifyProver::buildQuantifiedFormula");

  Context context = (Context)_isaved.pop();
  Connective con = (Connective)_isaved.pop();
  Formula* f = (Formula*)_built.pop();
  for (int i = _isaved.pop();i > 0;i--) { // i = number of formula to be prefixed with g
    f = new BinaryFormula(IMP,(Formula*)_built.pop(),f);
  }
  // undoing bindings
  List* vars = (List*)_saved.pop();
  while (vars) {
    // bind a new variable and add it to qvars
    string vname = vars->head()->str;
    unbindVar(vname);
    vars = vars->tail();
    if (! vars || keyword(vars->head()->str) != K_TYPE) {
      continue;
    }
    // the type of the variable id declared
    vars = vars->tail()->tail();
  }
  processFormula(new QuantifiedFormula(con,(IntList*)_built.pop(),f),context);
} // buildQuantifiedFormula

/**
 * Build an equality atom
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildEquality()
{
  CALL("SimplifyProver::buildEquality");
  Context context = (Context)_isaved.pop();
  int polarity = _isaved.pop();

  TermList r = _tsaved.pop();
  TermList l = _tsaved.pop();
  processFormula(new AtomicFormula(Literal::createEquality(polarity,l,r)),context);
} // buildEquality

/**
 * Build a DISTINCT formula
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::buildDistinct()
{
  CALL("SimplifyProver::buildDistinct");
  static DArray<TermList> args;

  Context context = (Context)_isaved.pop();
  int length = _isaved.pop();
  args.ensure(length);
  for (int i = length-1;i >= 0;i--) {
    args[i] = _tsaved.pop();
  }
  if (length == 2) {
    Literal* lit = Literal::createEquality(false,args[0],args[1]);
    processFormula(new AtomicFormula(lit),context);
    return;
  }
  FormulaList* fs = 0;
  for (int i = 1;i < length;i++) {
    for (int j = 0;j < i;j++) {
      Literal* lit = Literal::createEquality(false,args[i],args[j]);
      fs = new FormulaList(new AtomicFormula(lit));
    }
  }
  processFormula(new JunctionFormula(AND,fs),context);
} // buildDistinct


/**
 * Process a build formula depending on the context in which it was built
 * @since 01/09/2009, Redmond
 */
void SimplifyProver::processFormula(Formula* f,Context context)
{
  CALL("SimplifyProver::processFormula");

#if TRACE
  cout << "FORMULA: " << f->toString() << '\n';
#endif
  switch (context) {
  case CN_FORMULA:
    _built.push(f);
    return;
  case CN_TOP_LEVEL:
    {
      addUnit(new FormulaUnit(f,
			      new Inference(Inference::INPUT),
			      Unit::ASSUMPTION));
    }
    return;
  case CN_ARGUMENT:
    {
      Stack<TermList> args;
      FormulaVarIterator fvi(f);
      while (fvi.hasNext()) {
	TermList ts(fvi.next(),false);
	args.push(ts);
      }
      int arity = args.length();
      unsigned sf = env.signature->addSkolemFunction(arity);
      // term f(x)
      TermList fx(Term::create(sf,arity,args.begin()));
      // formula ~f => f(x) = 0
      Formula* f1 = new BinaryFormula(IMP,
				      new NegatedFormula(f),
				      new AtomicFormula(Literal::createEquality(true,fx,_zero)));
      addUnit(new FormulaUnit(f1,
			      new Inference(Inference::BOOLEAN_TERM_ENCODING),
			      Unit::AXIOM));
      f1 = new BinaryFormula(IMP,f,
			     new AtomicFormula(Literal::createEquality(true,fx,_one)));
      addUnit(new FormulaUnit(f1,
			      new Inference(Inference::BOOLEAN_TERM_ENCODING),
			      Unit::AXIOM));
      _tsaved.push(fx);
    }
    return;
  default:
    error("cannot handle formulas in a non-formula content");
  }
} // SimplifyProver::processFormula

/**
 * Add a constant that is a number. Introduced for adding axioms that all numbers are distinct
 * @since 03/09/2009 Redmond
 */
SimplifyProver::SymbolInfo* SimplifyProver::addNumber(const string& symb)
{
  CALL("SimplifyProver::addNumber");

  SymbolInfo* sinfo;
  if (_symbolInfo.find(symb,sinfo)) return sinfo;
  sinfo = new(0) SymbolInfo(0);
  sinfo->returnType = BIT_INT;
  unsigned snumber = env.signature->addFunction(symb,0);
  sinfo->number = snumber;
  _symbolInfo.insert(symb,sinfo);
  TermList num(Term::create(snumber,0,0));
  Stack<TermList>::Iterator ts(_numbers);
  while (ts.hasNext()) {
    TermList num1 = ts.next();
    Formula* ineq = new AtomicFormula(Literal::createEquality(false,num,num1));
    addUnit(new FormulaUnit(ineq,new Inference(Inference::THEORY),Unit::AXIOM));
  }
  _numbers.push(num);

  return sinfo;
} // SimplifyProver::addNumber

/**
 * Add a new unitt is a number. Introduced for adding axioms that all numbers are distinct
 * @since 03/09/2009 Redmond
 */
void SimplifyProver::addUnit(Unit* u)
{
  _units = new UnitList(u,_units);
#if TRACE
  cout << "UNIT: " << u->toString() << '\n';
#endif
} // SimplifyProver::addUnit

/**
 * Parse a formula under the negation connective from a list of expressions
 * @since 04/09/2009, Redmond
 */
void SimplifyProver::parseNegatedFormula(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseBinaryFormula");

  if (lst->length()!=1) formulaError(expr);
  _isaved.push(context);
  _commands.push(BUILD_NEGATED_FORMULA);

  _isaved.push(CN_FORMULA);
  _saved.push(lst->head());
  _commands.push(PARSE_FORMULA);
} // SimplifyProver::parseBinaryFormula
