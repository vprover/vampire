/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Token.hpp
 * Defines class Token
 *
 * @since 14/07/2004 Turku
 */

#ifndef __Token__
#define __Token__

#include "Lib/VString.hpp"

namespace Shell {

/**
 * Different token types.
 * @since 14/07/2004 Turku
 */
enum TokenType {
  /** non-negative integer */
  TT_INTEGER,
  /** real written as a floating point number */
  TT_REAL,
  /** '(' */
  TT_LPAR,
  /** ')' */
  TT_RPAR,
  /** '[' */
  TT_LBRA,
  /** ']' */
  TT_RBRA,
  /** ',' */
  TT_COMMA,
  /** ':' */
  TT_COLON,
  /** '.' */
  TT_DOT,
  /** '&amp;' */
  TT_AND,
  /** '~' */
  TT_NOT,
  /** '|' */
  TT_OR,
  /** '&lt;=&gt;' */
  TT_IFF,
  /** '=&gt;' */
  TT_IMP,
  /** '&lt;=' */
  TT_REVERSE_IMP,
  /** '&lt;~&gt;' */
  TT_XOR,
  /** '!' */
  TT_FORALL,
  /** '?' */
  TT_EXISTS,
  /** 'true' */
  TT_TRUE,
  /** 'false' */
  TT_FALSE,
  /** '++' */
  TT_PP,
  /** '--' */
  TT_MM,
  /** '=' */
  TT_EQUAL,
  /** '!=' */
  TT_NEQ,
  /** sequence of letters and digits beginning with a lower-case letter */
  TT_NAME,
  /** special tag for vampire(...) in the Vampire extension of the TPTP syntax */
  TT_VAMPIRE,
  /** sequence of letters and digits beginning with an upper-case letter */
  TT_VAR,
  /** input_formula */
  TT_INPUT_FORMULA, 
  /** input_clause */
  TT_INPUT_CLAUSE,
  /** cnf in the TPTP syntax */
  TT_CNF,
  /** include */
  TT_INCLUDE,
  /** end-of-file */
  TT_EOF,
  // KIF token types
  /** '\@...' */
  TT_ROW_VARIABLE,
  /** "..." */
  TT_STRING,
  /** '...' */
  TT_QUOTED_STRING,
  /** &gt; */
  TT_GREATER_THAN,
  /** &gt;= */
  TT_GEQ,
  /** &lt; */
  TT_LESS_THAN,
  /** &lt;= */
  TT_LEQ,
  /** /&gt; */
  TT_END_OF_EMPTY_TAG,
  /** any text inside an XML element */
  TT_TEXT,
  /** &lt;/ */
  TT_CLOSING_TAG,
  /** built-in addition */
  TT_PLUS,
  /** built-in subtraction */
  TT_MINUS,
  /** used in Simplify */
  TT_DISTINCT,
  /** used in Simplify */
  TT_LBLPOS,
  /** used in Simplify */
  TT_LBLNEG,
  /** used in Simplify */
  TT_LEMMA,
  /** used in Simplify */
  TT_PROOF,
  /** used in Simplify */
  TT_PUSH,
  /** used in Simplify */
  TT_POP,
  /** used in Simplify */
  TT_PATTERN,
  /** used in Simplify */
  TT_DEFPRED,
  /** used in Simplify */
  TT_DEFPREDMAP,
  /** used in Simplify */
  TT_PROMPTON,
  /** used in Simplify */
  TT_PROMPTOFF,
  /** used in Simplify */
  TT_ORDER,
  /** used in Simplify */
  TT_EXPLIES,
  /** addConstant() in MathSat */
  TT_ADD_CONSTANT,
  /** addVariable() in MathSat */
  TT_ADD_VARIABLE,
  /** addDefVariable() in MathSat */
  TT_ADD_DEF_VARIABLE,
  /** addEqual() in MathSat */
  TT_ADD_EQUAL,
  /** addBitNot() in MathSat */
  TT_ADD_BIT_NOT,
  /** addBitAnd() in MathSat */
  TT_ADD_BIT_AND,
  /** addBitOr() in MathSat */
  TT_ADD_BIT_OR,
  /** addBitXor() in MathSat */
  TT_ADD_BIT_XOR,
  /** addLogicalNot() in MathSat */
  TT_ADD_LOGICAL_NOT,
  /** addLogicalAnd() in MathSat */
  TT_ADD_LOGICAL_AND,
  /** addLogicalOr() in MathSat */
  TT_ADD_LOGICAL_OR,
  /** addLogicalImplies() in MathSat */
  TT_ADD_LOGICAL_IMPLIES,
  /** addLessThan() in MathSat */
  TT_ADD_LESS_THAN,
  /** addLessEqual() in MathSat */
  TT_ADD_LESS_EQUAL,
  /** addGreaterThan() in MathSat */
  TT_ADD_GREATER_THAN,
  /** addGreaterEqual() in MathSat */
  TT_ADD_GREATER_EQUAL,
  /** addSub() in MathSat */
  TT_ADD_SUB,
  /** addSum() in MathSat */
  TT_ADD_SUM,
  /** addMul() in MathSat */
  TT_ADD_MUL,
  /** addDiv() in MathSat */
  TT_ADD_DIV,
  /** addMod() in MathSat */
  TT_ADD_MOD,
  /** addLShift() in MathSat */
  TT_ADD_LSHIFT,
  /** addRShift() in MathSat */
  TT_ADD_RSHIFT,
  /** addLShift1() in MathSat */
  TT_ADD_LSHIFT1,
  /** addRShift1() in MathSat */
  TT_ADD_RSHIFT1,
  /** addAssignment() in MathSat */
  TT_ADD_ASSIGNMENT,
  /** addConcatOp() in MathSat */
  TT_ADD_CONCAT_OP,
  /** addCondition() in MathSat */
  TT_ADD_CONDITION,
  /** addZeroExtension() in MathSat */
  TT_ADD_ZERO_EXTENSION,
  /** addSignExtension() in MathSat */
  TT_ADD_SIGN_EXTENSION,
  /** addDefUF() in MathSat */
  TT_ADD_DEF_UF,
  /** addUFArg() in MathSat */
  TT_ADD_UF_ARG,
  /** addUFTermArg() in MathSat */
  TT_ADD_UF_TERM_ARG,
  /** addLatch() in MathSat */
  TT_ADD_LATCH,
  /** addUFTerm() in MathSat */
  TT_ADD_UF_TERM,
  /** addAssumption() in MathSat */
  TT_ADD_ASSUMPTION,
  /** attributes, start with ":" in SMT */
  TT_ATTRIBUTE,
  /** arithmetic characters in SMT */
  TT_ARITH,
  /** Use values in SMT */
  TT_USER
}; // TokenType


/**
 * Class representing tokens.
 */
class Token 
{
public:
  TokenType tag;
  Lib::vstring text;
  int line;

  static Lib::vstring toString (TokenType);
};

}

#endif // __Token__
