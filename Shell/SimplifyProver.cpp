
/*
 * File SimplifyProver.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SimplifyProver.cpp
 * Implements class SimplifyProver for working with files in the Simplify format
 *
 * @since 26/08/2009 Redmond
 */

#include "Lib/Exception.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/TermIterators.hpp"

#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "Options.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

// #define CALL(x) (cout << x << '\n')

// This are the keywords not handled yet:
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
//     K_ORDER,
//     K_MPAT,
//     K_PROMOTE,
//     K_EXPLIES,
//     K_PP,
//     K_DUMP_CTX,
//     K_ECHO,
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
  : _defaultSort(Sorts::SRT_DEFAULT),
    _numberSort(_defaultSort),
    _units(0),
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

  Map<vstring,SymbolInfo*>::Iterator it(_symbolInfo);
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
  CALL("SimplifyProver::parse/1");

  if (expr->tag == LispParser::ATOM) {
    switch (keyword(expr->str))
      {
      case K_DBG_WAS_VALID:
      case K_DBG_WAS_INVALID:
      case K_DBG_VALID:
      case K_DBG_INVALID:
				// ignore these commands
				return;
      default:
				error(expr->str + " not implemented\n");
      }
    return;
  }

  List* list = expr->list;
  Expression* head = list->head();
  if (head->tag == LispParser::LIST) {
		error("This kind of top-level expression is not implemented\n" + expr->toString());
	}
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
  case K_DEFPRED:
    defPred(list,expr);
    return;
  case K_SETPARAMETER: // ignore these parameters
    return;
  default: // should be the formula to prove
    _saved.push(expr);
    _commands.push(PARSE_FORMULA);
    _isaved.push(1); // goal
    _isaved.push(CN_TOP_LEVEL);
    parse();
    return;
  }
} // parse/1

/**
 * Return the keyword tag corresponding to the vstring @b str (K_NONE if not a keyword)
 * @since 26/08/2009 Redmond
 */
SimplifyProver::Keyword SimplifyProver::keyword(const vstring& str)
{
  CALL("SimplifyProver::keyword");

  if (str == "") {
    return K_NONE;
  }

  switch (str.at(0)) {
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
  default:
    break;
  }
  return K_NONE;
} // keyword

/** Create a typoinfo structure and allocate the argTypes array */
SimplifyProver::SymbolInfo::SymbolInfo(unsigned ar)
  : arity(ar)
{
}

/** allocate a new SymbolInfo structure */
void* SimplifyProver::SymbolInfo::operator new(size_t size, unsigned arity)
{
  return ALLOC_KNOWN(size + sizeof(int)*(arity-1),"SimplifyProver::SymbolInfo");
}

/** Bind a variable name to the variable number */
int SimplifyProver::bindVar(const vstring& varName)
{
  CALL("SimplifyProver::bindVar");

  IntList* bindings = 0;
  _variables.find(varName,bindings);
  bindings = new IntList(_nextVar,bindings);
  _variables.replaceOrInsert(varName,bindings);
  return _nextVar++;
} // bindVar

/** Unbind a variable name */
void SimplifyProver::unbindVar(const vstring& varName)
{
  CALL("SimplifyProver::unbindVar");

  IntList* bindings = 0;
  _variables.find(varName,bindings);
  IntList* tl = bindings->tail();
  delete bindings;
  bindings = tl;
  _variables.replaceOrInsert(varName,bindings);
} // bindVar

/**
 * Execute the next command stored in the stack of commands
 * @since 31/08/2009 Redmond
 */
void SimplifyProver::parse()
{
  CALL("SimplifyProver::parse");

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
    case BUILD_ITE_TERM:
      buildIfThenElseTerm();
      break;
    case DO_LET:
      doLet();
      break;
    case UNDO_LET:
      undoLet();
      break;
    case BUILD_LET_FORMULA:
      buildLetFormula();
      break;
    case BUILD_LET_TERM:
      buildLetTerm();
      break;
    case BIND_VARS:
      bindVars();
      break;
    case UNBIND_VARS:
      unbindVars();
      break;
    default:
      error((vstring)"Cannot handle command "+Int::toString(cmd));
    }
  }
  return;
} // parse()

/**
 * Report a formula parsing error and raise an exception.
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::formulaError(const Expression* expr)
{
  CALL("SimplifyProver::formulaError");
  error((vstring)"Formula " + expr->toString() + " cannot be parsed");
} // formulaError

/**
 * Report a formula parsing error and raise an exception.
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::formulaError(const Expression* expr,const char* explanation)
{
  CALL("SimplifyProver::formulaError");
  error((vstring)"Formula " + expr->toString() + " cannot be parsed" + ": " + explanation);
} // formulaError

/**
 * Report a term parsing error and raise an exception.
 * @since 31/08/2009 Redmond
 */
void SimplifyProver::termError(const Expression* expr)
{
  CALL("SimplifyProver::termError");
  error((vstring)"Term " + expr->toString() + " cannot be parsed");
} // termError

/**
 * Report and error and raise an exception.
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::error(const vstring& str)
{
  CALL("SimplifyProver::error");
  cerr << str << '\n';
  throw Exception(str);
} // error

/**
 * Parse a formula from an expression
 * The resulting formula will be pushed on the stack _built
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseFormula()
{
  CALL("SimplifyProver::parseFormula");

  const Expression* expr = (const Expression*)_saved.pop();
  Context context = (Context)_isaved.pop();
 retry:
  if (expr->tag == LispParser::LIST) {
    List* lst = expr->list;
    if (List::isEmpty(lst)) { // expression like (f)
      expr = lst->head();
    }
    else {
      vstring head = lst->head()->str;

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
      case K_LET:
	parseLet(lst->tail(),expr,context);
	return;
      case K_LBLNEG:
      case K_LBL:
      case K_LBLPOS:
	if (List::length(lst) != 3) {
	  formulaError(expr,"LBL expression has a wrong length");
	}
	expr = List::nth(lst, 2);
	goto retry;
      default:
	formulaError(expr);
      }
      return;
    }
  }

  // not list, an atom
  switch (keyword(expr->str)) {
  case K_NONE:
    parseAtom(expr,context);
    return;
  case K_TRUE:
    parseTrueFalse(true,context);
    return;
  case K_FALSE:
    parseTrueFalse(false,context);
    return;
  default:
    formulaError(expr,"unknown token");
  }
} // parseFormula

/**
 * Parse a quantified formula from a list of expressions
 * The resulting formula will be pushed on the stack _parsed
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseQuantifiedFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseQuantifiedFormula");

  Stack<int> booleanVars;
  lst = lst->tail();
  unsigned len = List::length(lst);
  if (len < 2) {
    formulaError(expr,"quantified formula too short");
  }
  // parsing variable sequence
  if (lst->head()->tag != LispParser::LIST) {
    formulaError(expr,"variable sequence should be a a list");
  }
  List* vars = lst->head()->list;
  for (List* vs = vars;vs;vs = vs->tail()) {
    if (vs->head()->tag == LispParser::LIST) formulaError(expr,"variable cannot be a list");
  }
  IntList* qvars = 0;
  IntList** qvarsTailPtr = &qvars;
  _saved.push(vars);
  while (vars) {
    // bind a new variable and add it to qvars
    vstring vname = vars->head()->str;
    if (keyword(vname) != K_NONE) {
      formulaError(expr,"keyword found where variable name expected");
    }
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
    if (! vars) {
      formulaError(expr,"wrong type declaration of a variable");
    }
    Type tp;
    if (! _types.find(vars->head()->str,tp)) {
      formulaError(expr,"type of variable not previously declared");
    }
    if (tp == BIT_BOOL) {
      booleanVars.push(varNumber);
    }
    vars = vars->tail();
  }
  _built.push(qvars);
  // if there are boolean variables in the quantifier, then the formula (A x)F should be changed
  // into (A x)(x=0 \/ x=1 -> F) and (E x) into (E x)((x=0 \/ x=1) & F)
  _isaved.push(booleanVars.length());
  while (! booleanVars.isEmpty()) {
    TermList x(booleanVars.pop(),false);
    Formula* l = new AtomicFormula(Literal::createEquality(true,x,_zero,_numberSort));
    Formula* r = new AtomicFormula(Literal::createEquality(true,x,_one,_numberSort));
    _built.push(new JunctionFormula(OR,
				    new FormulaList(l,
						    new FormulaList(r))));
  }

  lst = lst->tail();
  const Expression* ex = lst->head();
  while (lst->tail()) {
    if (ex->tag != LispParser::LIST) {
      formulaError(expr,"list (such as pattern declaration) expected");
    }
    switch (keyword(ex->list->head()->str)) {
    case K_QID: // ignore QID command
    case K_PATS: // ignore PATS command
    case K_NOPATS: // ignore NOPATS command
    case K_SKOLEMID: // ignore SKOLEMID command
    case K_WEIGHT: // ignore WEIGHT command
      lst = lst->tail();
      ex = lst->head();
      break;
    default:
      formulaError(expr,"pattern or weight declaration expected");
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
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseBinaryFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseBinaryFormula");

  if (List::length(lst) != 2) {
    formulaError(expr,"binary connective (such as <=>) must have two arguments");
  }
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
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseJunctionFormula(const List* lst,const Expression* expr,Connective c,Context context)
{
  CALL("SimplifyProver::parseJunctionFormula");

  if (List::length(lst) <= 2) formulaError(expr);
  lst = lst->tail();
  _isaved.push(List::length(lst));
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
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseAtom(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseAtom");
  ASS(!List::isEmpty(lst));
      
  if (lst->head()->tag == LispParser::LIST) {
    formulaError(expr);
  } 
  vstring symb = lst->head()->str;
  unsigned arity = List::length(lst) - 1;

  SymbolInfo* sinfo;
  if (!_symbolInfo.find(symb,sinfo)) {
    sinfo = builtInPredicate(symb,arity);
    if (! sinfo) {
      error((vstring)"predicate symbol " + symb + " not previously defined");
    }
  }
  _saved.push(sinfo);
  if (sinfo->arity != arity) {
    error((vstring)"predicate symbol " + symb + " is used with an arity different from declared");
  }
  if (sinfo->returnType != BIT_BOOL) {
    error((vstring)"symbol " + symb + " is used both as a function and as a predicate");
  }
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
 * Parse a formula TRUE or FALSE
 * @since 19/09/2009 Redmond
 */
void SimplifyProver::parseTrueFalse(bool tf,Context context)
{
  CALL("parseTrueFalse");

  switch (context) {
  case CN_TOP_LEVEL:
    {
      Formula* f = new Formula(tf);
      if (_isaved.pop()) { // goal
	f = new NegatedFormula(f);
	addUnit(new FormulaUnit(f,
				new Inference(Inference::NEGATED_CONJECTURE),
				Unit::CONJECTURE));
      }
      else { // assumption
	addUnit(new FormulaUnit(f,
				new Inference(Inference::INPUT),
				Unit::ASSUMPTION));
      }
      env.statistics->inputFormulas++;
    }
    return;
  case CN_FORMULA:
    processFormula(new Formula(tf),context);
    return;
  case CN_ARGUMENT:
    _tsaved.push(tf ? _one : _zero);
    return;
  }
} // parseTrueFalse

/**
 * Parse an atom from an atomic formula expressions
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseAtom(const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseAtom");

  vstring symb = expr->str;
  IntList* bindings;
  if (_variables.find(symb,bindings) && bindings) {
    // a boolean variable
    TermList v(bindings->head(),false);
    switch (context) {
    case CN_TOP_LEVEL:
      ASSERTION_VIOLATION;
    case CN_FORMULA:
      processFormula(new AtomicFormula(Literal::createEquality(true,v,_one,_numberSort)),context);
      return;
    case CN_ARGUMENT:
      _tsaved.push(v);
      return;
    }
  }

  Lib::List<Formula*>* binding = 0;
  _formulaLet.find(symb,binding);
  if (Lib::List<Formula*>::isNonEmpty(binding)) {
    processFormula(binding->head(),context);
    return;
  }

  SymbolInfo* sinfo;
  if (!_symbolInfo.find(symb,sinfo)) {
    sinfo = builtInPredicate(symb,0);
    if (! sinfo) error((vstring)"predicate symbol " + symb + " not previously defined");
  }
  if (sinfo->arity != 0) error((vstring)"predicate symbol " + symb + " is used with an arity different from declared");
  if (sinfo->returnType != BIT_BOOL) error((vstring)"symbol " + symb + " is used both as a function and as a predicate");

  Literal* lit = Literal::create(sinfo->number,0,true,false,0);
  processFormula(new AtomicFormula(lit),context);
} // parseAtom

/**
 * Parse a DISTINCT formula
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::parseDistinct(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseDistinct");
  ASS(List::isNonEmpty(lst));
  
  lst = lst->tail();
  unsigned length = List::length(lst);
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
 * Parse a LET formula
 * @since 11/09/2009 Redmond
 */
void SimplifyProver::parseLet(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseLet");

  if (List::length(lst) != 2) formulaError(expr);
  Expression* let = lst->head();
  if (let->tag == LispParser::ATOM) formulaError(expr);
  // bindings produced by LET
  _saved.push(let->list);
  _commands.push(UNDO_LET);
  _saved.push(lst->tail()->head());
  _isaved.push(context);
  _commands.push(PARSE_FORMULA);
  _saved.push(expr);
  _saved.push(let->list);
  _commands.push(DO_LET);
} // parseLet

/**
 * Parse an equality atom
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::parseEquality(const List* lst,const Expression* expr,Context context,bool polarity)
{
  CALL("SimplifyProver::parseEquality");

  if (List::length(lst) != 3) formulaError(expr);
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
 * @since 29/08/2009 Redmond
 */
SimplifyProver::SymbolInfo* SimplifyProver::builtInPredicate(const vstring& symb,unsigned arity)
{
  CALL("SimplifyProver::builtInPredicate");

  bool isEquality = false;
#if 0
  if (symb == ">=") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedPredicate(symb,Theory::INT_GREATER_EQUAL);
  }
  else if (symb == ">") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedPredicate(symb,Theory::INT_GREATER);
  }
  else if (symb == "<=") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedPredicate(symb,Theory::INT_LESS_EQUAL);
  }
  else if (symb == "<") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedPredicate(symb,Theory::INT_LESS);
  }
  else
#endif
  if (symb == "EQ") {
      if (arity != 2) return 0;
      isEquality = true;
  }

  SymbolInfo* sinfo = new(arity) SymbolInfo(arity);
  sinfo->returnType = BIT_BOOL;
  sinfo->number = isEquality ? 0 : env.signature->addPredicate(symb,arity);
  for (unsigned i = 0;i < arity;i++) {
    sinfo->argTypes[i] = BIT_INT;
  }
  _symbolInfo.insert(symb,sinfo);
  return sinfo;
} // SimplifyProver::builtInPredicate

/**
 * True if symb is a built-in function. Built-in functions do not
 * have to be declared in advance but they can be used.
 * @since 31/08/2009 Redmond
 */
SimplifyProver::SymbolInfo* SimplifyProver::builtInFunction(const vstring& symb, unsigned arity)
{
  CALL("SimplifyProver::builtInFunction");

#if 0
  if (symb == "+") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedFunction(symb,Theory::PLUS);
  }
  else if (symb == "-") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedFunction(symb,Theory::MINUS);
  }
  else if (symb == "*") {
    if (arity != 2) return 0;
    env.options->setTheoryAxioms(true);
    env.signature->registerInterpretedFunction(symb,Theory::MULTIPLY);
  }
#endif
  SymbolInfo* sinfo = new(arity) SymbolInfo(arity);
  sinfo->returnType = BIT_INT;
  sinfo->number = env.signature->addFunction(symb,arity);
  for (unsigned i = 0;i < arity;i++) {
    sinfo->argTypes[i] = BIT_INT;
  }

  _symbolInfo.insert(symb,sinfo);
  return sinfo;
} // SimplifyProver::builtInFunction

/**
 * Parse a term from a list of expressions
 * @since 29/08/2009 Redmond
 */
void SimplifyProver::parseTerm()
{
  CALL("SimplifyProver::parseTerm");

  const Expression* expr = (const Expression*)_saved.pop();
  if (expr->tag == LispParser::ATOM) {
    vstring symb = expr->str;
    if (keyword(symb) != K_NONE) {
      error((vstring)"term expected: " + expr->toString());
    }
    if (Int::isInteger(symb)) {
#if 0
      InterpretedType val;
      if(!Int::stringToInt(symb,val)) {
        error((vstring)"unsupported integer value: " + symb);
      }

      TermList ts;
      Term* t = theory->getRepresentation(val);
      ts.setTerm(t);
      _tsaved.push(ts);
#else
      INVALID_OPERATION("Integers not supported by the Simplify parser currently");
#endif
      return;
    }

    IntList* bindings;
    if (_variables.find(symb,bindings) && bindings) {
      TermList ts(bindings->head(),false);
      _tsaved.push(ts);
      return;
    }
    Lib::List<TermList>* binding = 0;
    _termLet.find(symb,binding);
    if (binding) {
      _tsaved.push(binding->head());
      return;
    }

    SymbolInfo* sinfo;
    if (!_symbolInfo.find(symb,sinfo)) {
      sinfo = builtInFunction(symb,0);
      if (! sinfo) {
	error((vstring)"function symbol " + symb + " not previously defined");
      }
    }
    if (sinfo->arity != 0) {
      error((vstring)"function symbol " + symb + " is used with an arity different from declared");
    }
    if (sinfo->returnType == BIT_BOOL) {
      error((vstring)"symbol " + symb + " is used both as a constant and as a predicate");
    }
    TermList ts;
    Term* t = Term::create(sinfo->number,0,0);
    ts.setTerm(t);
    _tsaved.push(ts);
    return;
  }

  // list
  List* lst = expr->list;
  if (lst->head()->tag == LispParser::LIST) {
    termError(expr);
  }
  vstring symb = lst->head()->str;
  switch (keyword(symb)) {
  case K_NONE:
    {
      unsigned arity = List::length(lst) - 1;
      SymbolInfo* sinfo;
      if (!_symbolInfo.find(symb,sinfo)) {
	sinfo = builtInFunction(symb,arity);
	if (! sinfo) {
	  error((vstring)"function symbol " + symb + " not previously defined");
	}
      }
      _saved.push(sinfo);
      if (sinfo->arity != arity) {
	error((vstring)"function symbol " + symb + " is used with an arity different from declared");
      }
      if (sinfo->returnType == BIT_BOOL) {
	error((vstring)"symbol " + symb + " is used both as a function and as a predicate");
      }
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
    }
    return;
  case K_ITE:
    _commands.push(BUILD_ITE_TERM);
    lst = lst->tail();
    _saved.push(lst->head());
    _isaved.push(CN_FORMULA);
    _commands.push(PARSE_FORMULA);
    lst = lst->tail();
    _saved.push(lst->head());
    _commands.push(PARSE_TERM);
    lst = lst->tail();
    _saved.push(lst->head());
    _commands.push(PARSE_TERM);
    return;

  default:
    error((vstring)"term expected: " + expr->toString());
  }
} // parseTerm

/**
 * Parse a DEFTYPE declaration
 * @since 31/08/2009 Redmond
 */
void SimplifyProver::defType(const List* lst,const Expression* expr)
{
  CALL("SimplifyProver::defType");

  unsigned length = List::length(lst);
  if (length == 0) {
  err:
    error((vstring)"Bad DEFTYPE declaration " + expr->toString());
  }
  List* l1 = lst->tail();
  Expression* h1 = l1->head();
  if (h1->tag == LispParser::LIST) {
    goto err;
  }
  vstring typeName = h1->str;
  if (keyword(typeName) != K_NONE) {
    goto err;
  }
      
  if (length == 2) {
    _types.insert(typeName,(Type)_nextType);
    _nextType++;
    return;
  }
  if (length < 4 || length > 5) goto err;
  List* l2 = l1->tail();
  if (l2->head()->tag == LispParser::LIST) {
    goto err;
  }
  if (keyword(l2->head()->str) != K_BUILTIN) {
    goto err;
  }
  List* l3 = l2->tail();
  if (l3->head()->tag == LispParser::LIST) {
    goto err;
  }
  Type tp;
  if (l3->head()->str == "Int" && length == 4) {
    tp = BIT_INT;
  }
  else if (l3->head()->str == "bool" && length == 4) {
    tp = BIT_BOOL;
  }
  else if (l3->head()->str == "BitVec" && length == 5) {
    // the length of the bit-vector is ignored
    tp = BIT_BITVEC;
  }
  else {
    goto err;
  }
  _types.insert(typeName,tp);
} // SimplifyProver::defType

/**
 * Parse a DEFOP declaration
 * @since 31/08/2009 Redmond
 */
void SimplifyProver::defOp(const List* list,const Expression* expr)
{
  CALL("SimplifyProver::defOp");

  Stack<Type> types;
  List* l1 = list->tail();
  Expression* h1 = l1->head();
  if (h1->tag == LispParser::LIST) {
  err:
    error((vstring)"Bad DEFOP declaration: " + expr->toString());
  }
  vstring symb = h1->str;
  if (keyword(symb) != K_NONE) {
    goto err;
  }
  List::Iterator lit(l1->tail());
  bool done = false;
  while (lit.hasNext()) {
    h1 = lit.next();
    if (h1->tag == LispParser::LIST) {
      goto err;
    }
    vstring typeName = h1->str;
    switch (keyword(typeName)) {
    case K_NONE:
      break;
    case K_BUILTIN:
      done = true;
      break;
    default:
      goto err;
    }
    if (done) break;
    Type tp;
    if (! _types.find(typeName,tp)) error((vstring)"Type " + typeName + " not declared in " + expr->toString());
    if (tp == BIT_BOOL) {
      _hasBooleanArgs.insert(symb);
    }
    types.push(tp);
  }

  unsigned length = types.length();
  if (length == 0) goto err;
  SymbolInfo* symInfo = new(length-1) SymbolInfo(length-1);
  Type tp = types.pop();
  symInfo->returnType = tp;
  for (unsigned i = 0;i < length-1;i++) {
    symInfo->argTypes[i] = types[i];
  }

  if (tp == BIT_BOOL) {
    symInfo->number = env.signature->addPredicate(symb,length-1);
  }
  else {
    symInfo->number = env.signature->addFunction(symb,length-1);
  }
  _symbolInfo.insert(symb,symInfo);
} // SimplifyProver::defOp

/**
 * Parse a BG_PUSH command. To avoid very large formulas in the proofs we use the following
 * trick: if the argument of BG_PUSH is a conjuction, we split it as if it were several
 * BG_PUSH declarations.
 * @since 31/08/2009 Redmond
 */
void SimplifyProver::bgPush(const List* list)
{
  CALL("SimplifyProver::bgPush");

  Stack<const List*> in;
  in.push(list->tail());
  Stack<const Expression*> out;
  while (! in.isEmpty()) {
    list = in.pop();
    if (List::isEmpty(list)) continue;
    in.push(list->tail());
    const Expression* ex = list->head();
    if (ex->tag == LispParser::LIST) {
      list = ex->list;
      if (List::isEmpty(list)) {
	formulaError(ex);
      }
      const Expression* hd = list->head();
      if (hd->tag == LispParser::ATOM &&
	  keyword(hd->str) == K_AND) {
	in.push(list->tail());
	continue;
      }
    }
    out.push(ex);
  }
  while (! out.isEmpty()) {
    _saved.push(out.pop());
    _commands.push(PARSE_FORMULA);
    _isaved.push(0); // assumption
    _isaved.push(CN_TOP_LEVEL);
  }
  parse();
} // bgPush

/**
 * Parse a DEFPRED command
 * @param list the list expression (DEFPRED ...)
 * @param listExpr the expression containing listExpr (only for error messages)
 * @since 29/07/2010 Linz
 */
void SimplifyProver::defPred(const List* list,const Expression* listExpr)
{
  CALL("SimplifyProver::defPred");

  // skip DEFPRED
  list = list->tail();
  if (! list->tail()) {
    error("empty DEFPRED definition: " + listExpr->toString());
  }
  Expression* lhs = list->head();
  list = list->tail();
  if (! list) {
    error("incomplete DEFPRED definition: " + listExpr->toString());
  }
  if (list->tail()) {
    error("incorrect DEFPRED definition: " + listExpr->toString());
  }
  Expression* rhs = list->head();

  // in the lhs of DEFPRED (F x1 ... xn) the xi are variables, although they are
  // not quantified, so we add commands to make them variables and then back
  // non-variables
  List* vars;
  if (lhs->tag != LispParser::LIST) {
    vars = 0;
  }
  else {
    List* args = lhs->list;
    if (List::isEmpty(args)) {
      error("incorrect DEFPRED definition: " + listExpr->toString());
    }
    vars = args->tail();
  }
  _saved.push(vars);
  _commands.push(UNBIND_VARS);

  // save commands to build equivalence after building lhs and rhs
  _isaved.push(0); // assumption
  _isaved.push(IFF);
  _isaved.push(CN_TOP_LEVEL);
  _commands.push(BUILD_BINARY_FORMULA);

  // command to build the lhs of the definition
  _saved.push(lhs);
  _commands.push(PARSE_FORMULA);
  _isaved.push(CN_FORMULA);

  // command to build the rhs of the definition
  _isaved.push(CN_FORMULA);
  _saved.push(rhs);
  _commands.push(PARSE_FORMULA);

  _saved.push(vars);
  _commands.push(BIND_VARS);

  parse();
} // defPred

/**
 * Build a parsed term
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildTerm()
{
  CALL("SimplifyProver::buildTerm");
  static DArray<TermList> args;

  const SymbolInfo* sinfo = (SymbolInfo*)_saved.pop();
  unsigned arity = sinfo->arity;
  args.ensure(arity);
  for (unsigned i = 0;i < arity;i++) {
    args[i] = _tsaved.pop();
  }
  TermList ts(Term::create(sinfo->number,arity,args.array()));
  _tsaved.push(ts);
} // buildTerm

/**
 * Build a parsed atom
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildAtom()
{
  CALL("SimplifyProver::buildAtom");
  static DArray<TermList> args;

  const SymbolInfo* sinfo = (SymbolInfo*)_saved.pop();
  Context context = (Context)_isaved.pop();
  unsigned arity = sinfo->arity;
  args.ensure(arity);
  for (unsigned i = 0;i < arity;i++) {
    args[i] = _tsaved.pop();
  }
  Literal* lit = sinfo->number == 0 // equality
    ? Literal::createEquality(true,args[0],args[1],_defaultSort)
    : Literal::create(sinfo->number,arity,true,false,args.array());
  processFormula(new AtomicFormula(lit),context);
} // buildAtom

/**
 * Build a binary formula
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildBinaryFormula()
{
  CALL("SimplifyProver::buildBinaryFormula");

  Context context = (Context)_isaved.pop();
  Connective con = (Connective)_isaved.pop();

  Formula* l = (Formula*)_built.pop();
  Formula* r = (Formula*)_built.pop();
  processFormula(new BinaryFormula(con,l,r),context);
} // buildBinaryFormula

/**
 * Build a negated formula
 * @since 04/09/2009 Redmond
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
 * @since 01/09/2009 Redmond
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
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildQuantifiedFormula()
{
  CALL("SimplifyProver::buildQuantifiedFormula");

  Context context = (Context)_isaved.pop();
  Connective con = (Connective)_isaved.pop();
  Formula* f = (Formula*)_built.pop();
  for (int i = _isaved.pop();i > 0;i--) { // i = number of formula to be prefixed with g
    Formula* guard = (Formula*)_built.pop();
    if (con == FORALL) {
      f = new BinaryFormula(IMP,guard,f);
    }
    else {
      f = new JunctionFormula(AND,
			      new FormulaList(guard,
					      new FormulaList(f)));
    }
  }
  // undoing bindings
  List* vars = (List*)_saved.pop();
  while (vars) {
    // bind a new variable and add it to qvars
    vstring vname = vars->head()->str;
    unbindVar(vname);
    vars = vars->tail();
    if (! vars || keyword(vars->head()->str) != K_TYPE) {
      continue;
    }
    // the type of the variable id declared
    vars = vars->tail()->tail();
  }
  processFormula(new QuantifiedFormula(con,(IntList*)_built.pop(),0,f),context);
} // buildQuantifiedFormula

/**
 * Build an equality atom
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildEquality()
{
  CALL("SimplifyProver::buildEquality");
  Context context = (Context)_isaved.pop();
  int polarity = _isaved.pop();

  TermList l = _tsaved.pop();
  TermList r = _tsaved.pop();
  processFormula(new AtomicFormula(Literal::createEquality(polarity,l,r,_defaultSort)),context);
} // buildEquality

/**
 * Do bindings introduced by LET
 * @since 13/09/2009 Redmond
 */
void SimplifyProver::doLet()
{
  CALL("SimplifyProver::doLet");

  const List* lst = (const List*)_saved.pop();
  if (List::isEmpty(lst)) {
    _saved.pop();
    return;
  }
  _saved.push(lst->tail());
  _commands.push(DO_LET);

  const Expression* hd = lst->head();
  if (hd->tag == LispParser::ATOM) {
  err:
    _saved.pop();
    const Expression* expr = (const Expression*)_saved.top();
    formulaError(expr);
  }
  lst = hd->list;
  if (List::length(lst) != 3) goto err;
  hd = lst->head(); // hd is either FORMULA or TERM
  if (hd->tag == LispParser::LIST) {
    goto err;
  }
  lst = lst->tail();
  switch (keyword(hd->str)) {
  case K_FORMULA:
    _ssaved.push(lst->head()->str);
    _commands.push(BUILD_LET_FORMULA);
    _isaved.push(CN_FORMULA);
    _saved.push(lst->tail()->head());
    _commands.push(PARSE_FORMULA);
    return;
  case K_TERM:
    _ssaved.push(lst->head()->str);
    _commands.push(BUILD_LET_TERM);
    _saved.push(lst->tail()->head());
    _commands.push(PARSE_TERM);
    return;
  default:
    goto err;
  }
} // doLet

/**
 * Undo bindings introduced by LET
 * @since 13/09/2009 Redmond
 */
void SimplifyProver::undoLet()
{
  CALL("SimplifyProver::undoLet");
  for (const List* lst = (const List*)_saved.pop();List::isNonEmpty(lst); lst=lst->tail()) {
    const List* bind = lst->head()->list;
    vstring symb = bind->tail()->head()->str;
    switch (keyword(bind->head()->str)) {
    case K_FORMULA:
      {
	Lib::List<Formula*>* binding;
	_formulaLet.find(symb,binding);
	_formulaLet.replace(symb,binding->tail());
	delete binding;
      }
      return;
    case K_TERM:
      {
	Lib::List<TermList>* binding;
	_termLet.find(symb,binding);
	_termLet.replace(symb,binding->tail());
	delete binding;
      }
      return;
    default: // though only K_TERM is possible here
      return;
    }
  }
} // undoLet

/**
 * Build a DISTINCT formula
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::buildDistinct()
{
  CALL("SimplifyProver::buildDistinct");
  static DArray<TermList> args;

  Context context = (Context)_isaved.pop();
  unsigned length = (unsigned)_isaved.pop();
  args.ensure(length);
  for (int i = length-1;i >= 0;i--) {
    args[i] = _tsaved.pop();
  }
  if (length == 2) {
    Literal* lit = Literal::createEquality(false,args[0],args[1],_defaultSort);
    processFormula(new AtomicFormula(lit),context);
    return;
  }
  FormulaList* fs = 0;

  bool top = (context == CN_TOP_LEVEL) && ! _isaved.top();
  // TEMPORARY, only 300 are processed
  if (length > 300) length = 300;
  for (unsigned i = 1;i < length;i++) {
    for (unsigned j = 0;j < i;j++) {
      Literal* lit = Literal::createEquality(false,args[i],args[j],_defaultSort);
      Formula* ineq = new AtomicFormula(lit);
      if (top) {
	addUnit(new FormulaUnit(ineq,
				new Inference(Inference::INPUT),
				Unit::ASSUMPTION));
      }
      else {
	fs = new FormulaList(ineq,fs);
      }
    }
  }
  if (top) {
    _isaved.pop();
  }
  else {
    processFormula(new JunctionFormula(AND,fs),context);
  }
} // buildDistinct

/**
 * Process a build formula depending on the context in which it was built
 * @since 01/09/2009 Redmond
 */
void SimplifyProver::processFormula(Formula* f,Context context)
{
  CALL("SimplifyProver::processFormula");

  switch (context) {
  case CN_FORMULA:
    _built.push(f);
    return;
  case CN_TOP_LEVEL:
    if (_isaved.pop()) { // goal
      Formula::VarList* vs = f->freeVariables();
      if (Formula::VarList::isEmpty(vs)) {
	f = new NegatedFormula(f);
      }
      else {
	f = new NegatedFormula(new QuantifiedFormula(FORALL,vs,0,f));
      }
      addUnit(new FormulaUnit(f,
			      new Inference(Inference::NEGATED_CONJECTURE),
			      Unit::CONJECTURE));
    }
    else { // assumption
      addUnit(new FormulaUnit(f,
			      new Inference(Inference::INPUT),
			      Unit::ASSUMPTION));
    }
    env.statistics->inputFormulas++;
    return;
  case CN_ARGUMENT:
    {
      Stack<TermList> args;
      FormulaVarIterator fvi(f);
      while (fvi.hasNext()) {
	TermList ts(fvi.next(),false);
	args.push(ts);
      }
      unsigned arity = args.length();
      unsigned sf = env.signature->addSkolemFunction(arity);
      // term f(x)
      TermList fx(Term::create(sf,arity,args.begin()));
      // formula ~f => f(x) = 0
      Formula* f1 = new BinaryFormula(IMP,
				      new NegatedFormula(f),
				      new AtomicFormula(Literal::createEquality(true,fx,_zero,_numberSort)));
      addUnit(new FormulaUnit(f1,
			      new Inference(Inference::BOOLEAN_TERM_ENCODING),
			      Unit::AXIOM));
      f1 = new BinaryFormula(IMP,f,
			     new AtomicFormula(Literal::createEquality(true,fx,_one,_numberSort)));
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
SimplifyProver::SymbolInfo* SimplifyProver::addNumber(const vstring& symb)
{
  CALL("SimplifyProver::addNumber");

  SymbolInfo* sinfo = 0;
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
    Formula* ineq = new AtomicFormula(Literal::createEquality(false,num,num1,_numberSort));
    addUnit(new FormulaUnit(ineq,new Inference(Inference::SIMPLIFY_PROVER_DISTINCT_NUMBERS_AXIOM),Unit::AXIOM));
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
} // SimplifyProver::addUnit

/**
 * Parse a formula under the negation connective from a list of expressions
 * @since 04/09/2009 Redmond
 */
void SimplifyProver::parseNegatedFormula(const List* lst,const Expression* expr,Context context)
{
  CALL("SimplifyProver::parseNegatedFormula");

  if (List::length(lst) != 1) {
    formulaError(expr);
  }
  _isaved.push(context);
  _commands.push(BUILD_NEGATED_FORMULA);

  _isaved.push(CN_FORMULA);
  _saved.push(lst->head());
  _commands.push(PARSE_FORMULA);
} // SimplifyProver::parseNegatedFormula

/**
 * Build an if-then-else term
 * @since 14/09/2009 Redmond
 */
void SimplifyProver::buildIfThenElseTerm()
{
  CALL("SimplifyProver::buildIfThenElseTerm");

  Formula* f = (Formula*)_built.pop();
  TermList s = _tsaved.pop();
  TermList t = _tsaved.pop();
  Stack<TermList> args;
  FormulaVarIterator fit(f);
  MultiCounter mc;
  while (fit.hasNext()) {
    unsigned v = fit.next();
    mc.inc(v);
    TermList ts(v,false);
    args.push(ts);
  }
  if (s.isVar()) {
    unsigned v = s.var();
    if (! mc.get(v)) {
      mc.inc(v);
      TermList ts(v,false);
      args.push(ts);
    }
  }
  else {
    TermVarIterator tit(s.term()->args());
    while (tit.hasNext()) {
      unsigned v = tit.next();
      if (mc.get(v)) continue;
      mc.inc(v);
      TermList ts(v,false);
      args.push(ts);
    }
  }
  if (t.isVar()) {
    unsigned v = t.var();
    if (! mc.get(v)) {
      mc.inc(v);
      TermList ts(v,false);
      args.push(ts);
    }
  }
  else {
    TermVarIterator tit(t.term()->args());
    while (tit.hasNext()) {
      unsigned v = tit.next();
      if (mc.get(v)) continue;
      mc.inc(v);
      TermList ts(v,false);
      args.push(ts);
    }
  }
  unsigned arity = args.length();
  unsigned sf = env.signature->addSkolemFunction(arity);
  TermList fx(Term::create(sf,arity,args.begin()));
  // add axioms f => fx=s and ~f => fx=t
 
  Formula* fxs = new AtomicFormula(Literal::createEquality(true,fx,s,_defaultSort));
  Formula* fxt = new AtomicFormula(Literal::createEquality(true,fx,t,_defaultSort));

  Formula* f1 = new BinaryFormula(IMP,f,fxs);
  Formula* f2 = new BinaryFormula(IMP,new NegatedFormula(f),fxt);
  addUnit(new FormulaUnit(f1,
			  new Inference(Inference::FOOL_ITE_ELIMINATION),
			  Unit::AXIOM));
  addUnit(new FormulaUnit(f2,
			  new Inference(Inference::FOOL_ITE_ELIMINATION),
			  Unit::AXIOM));
  // and save the term fx as the result
  _tsaved.push(fx);
} // buildIfThenElseTerm

/**
 * Build a definition introduced by the LET expression for formulas
 * @since 18/09/2009 Redmond
 */
void SimplifyProver::buildLetFormula()
{
  CALL("SimplifyProver::buildLetFormula");

  Formula* f = (Formula*)_built.pop();
  vstring symb = _ssaved.pop();
  FormulaVarIterator fvi(f);
  Stack<TermList> args;
  while (fvi.hasNext()) {
    args.push(TermList(fvi.next(),false));
  }
  unsigned arity = args.length();
  unsigned sf = env.signature->addNamePredicate(arity);
  // atom p(x)
  Formula* px = new AtomicFormula(Literal::create(sf,arity,true,false,args.begin()));
  // add binding to the let-stack
  Lib::List<Formula*>* binding = 0;
  _formulaLet.find(symb,binding);
  binding = new Lib::List<Formula*>(px,binding);
  _formulaLet.replaceOrInsert(symb,binding);
  _isaved.push(0); // assumption
  processFormula(new BinaryFormula(IFF,px,f),CN_TOP_LEVEL);
} // SimplifyProver::buildLetFormula

/**
 * Build a definition introduced by the LET expression for terms
 * @since 18/09/2009 Redmond
 */
void SimplifyProver::buildLetTerm()
{
  CALL("SimplifyProver::buildLetTerm");

  TermList s = _tsaved.pop();
  vstring symb = _ssaved.pop();

  // add binding to the let-stack
  Lib::List<TermList>* binding = 0;
  _termLet.find(symb,binding);
  binding = new Lib::List<TermList>(s,binding);
  _termLet.replaceOrInsert(symb,binding);
} // SimplifyProver::buildLetTerm

/**
 * Bind list of variables stored ib in _saved
 * @since 29/11/2010 Linz
 */
void SimplifyProver::bindVars()
{
  CALL("SimplifyProver::bindVars");

  List* vs = (List*)(_saved.pop());
  List::Iterator vit(vs);
  while (vit.hasNext()) {
    Expression* v = vit.next();
    if (v->tag == LispParser::LIST) {
      error("Variable expected: " + v->toString());
    }
    bindVar(v->str);
  }
}

/**
 * Unbind list of variables stored ib in _saved
 * @since 29/11/2010 Linz
 */
void SimplifyProver::unbindVars()
{
  CALL("SimplifyProver::unbindVars");

  List* vs = (List*)(_saved.pop());
  List::Iterator vit(vs);
  while (vit.hasNext()) {
    Expression* v = vit.next();
    unbindVar(v->str);
  }
}
