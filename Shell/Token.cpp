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
 * @file Token.cpp
 * Implements class Token
 *
 * @since 25/07/2004 Torrevieja
 */

#include "Debug/Assertion.hpp"
#include "Token.hpp"

using namespace std;

namespace Shell {

/**
 * Return a text representation of a token.
 * 
 * @since 25/07/2004 Torrevieja
 */
Lib::vstring Token::toString (TokenType tt)
{
  switch (tt) {
  case TT_INTEGER:
    return "<integer>";
  case TT_REAL:
    return "<real>";
  case TT_ROW_VARIABLE:
    return "<row variable>";
  case TT_STRING:
    return "<string>";
  case TT_EOF:
    return "<end-of-file>";
  case TT_LPAR:
    return "(";
  case TT_RPAR:
    return ")";
  case TT_LBRA:
    return "[";
  case TT_RBRA:
    return "]";
  case TT_COMMA:
    return ",";
  case TT_COLON:
    return ":";
  case TT_DOT  :
    return ".";
  case TT_AND:
    return "&";
  case TT_NOT:
    return "~";
  case TT_OR:
    return "|";
  case TT_IFF:
    return "<=>";
  case TT_IMP:
    return "=>";
  case TT_REVERSE_IMP:
    return "<=";
  case TT_XOR:
    return "<~>";
  case TT_FORALL:
    return "!";
  case TT_EXISTS:
    return "?";
  case TT_PP:
    return "++";
  case TT_MM:
    return "--";
  case TT_EQUAL:
    return "=";
  case TT_NAME:
    return "<name>";
  case TT_VAMPIRE:
    return "vampire(...)";
  case TT_VAR:
    return "<variable>";
  case TT_INPUT_FORMULA: 
    return "input_formula";
  case TT_INPUT_CLAUSE:
    return "input_clause";
  case TT_INCLUDE:
    return "include";
  case TT_GREATER_THAN:
    return ">";
  case TT_LESS_THAN:
    return "<";
  case TT_END_OF_EMPTY_TAG:
    return "/>";
  case TT_TEXT:
    return "<text>";
  case TT_CLOSING_TAG:
    return "</";
  case TT_PLUS:
    return "plus";
  case TT_MINUS:
    return "minus";
  case TT_DISTINCT:
    return "distinct";
  case TT_LBLPOS:
    return "LBLPOS";
  case TT_LBLNEG:
    return "LBLNEG";
  case TT_LEMMA:
    return "LEMMA";
  case TT_PROOF:
    return "PROOF";
  case TT_PUSH:
    return "PUSH";
  case TT_POP:
    return "POP";
  case TT_PATTERN:
    return "PATTERN";
  case TT_DEFPRED:
    return "DEFPRED";
  case TT_DEFPREDMAP:
    return "DEFPREDMAP";
  case TT_PROMPTON:
    return "PROMPTON";
  case TT_PROMPTOFF:
    return "PROMPTOFF";
  case TT_ORDER:
    return "ORDER";
  case TT_EXPLIES:
    return "EXPLIES";
  case TT_ADD_CONSTANT:
    return "ADD_CONSTANT";
  case TT_ADD_VARIABLE:
    return "ADD_VARIABLE";
  case TT_ADD_DEF_VARIABLE:
    return "ADD_DEF_VARIABLE";
  case TT_ADD_EQUAL:
    return "ADD_EQUAL";
  case TT_ADD_BIT_NOT:
    return "ADD_BIT_NOT";
  case TT_ADD_BIT_AND:
    return "ADD_BIT_AND";
  case TT_ADD_BIT_OR:
    return "ADD_BIT_OR";
  case TT_ADD_BIT_XOR:
    return "ADD_BIT_XOR";
  case TT_ADD_LOGICAL_NOT:
    return "ADD_LOGICAL_NOT";
  case TT_ADD_LOGICAL_AND:
    return "ADD_LOGICAL_AND";
  case TT_ADD_LOGICAL_OR:
    return "ADD_LOGICAL_OR";
  case TT_ADD_LOGICAL_IMPLIES:
    return "ADD_LOGICAL_IMPLIES";
  case TT_ADD_LESS_THAN:
    return "ADD_LESS_THAN";
  case TT_ADD_LESS_EQUAL:
    return "ADD_LESS_EQUAL";
  case TT_ADD_GREATER_THAN:
    return "ADD_GREATER_THAN";
  case TT_ADD_GREATER_EQUAL:
    return "ADD_GREATER_EQUAL";
  case TT_ADD_SUB:
    return "ADD_SUB";
  case TT_ADD_SUM:
    return "ADD_SUM";
  case TT_ADD_MUL:
    return "ADD_MUL";
  case TT_ADD_DIV:
    return "ADD_DIV";
  case TT_ADD_MOD:
    return "ADD_MOD";
  case TT_ADD_LSHIFT:
    return "ADD_LSHIFT";
  case TT_ADD_RSHIFT:
    return "ADD_RSHIFT";
  case TT_ADD_LSHIFT1:
    return "ADD_LSHIFT1";
  case TT_ADD_RSHIFT1:
    return "ADD_RSHIFT1";
  case TT_ADD_ASSIGNMENT:
    return "ADD_ASSIGNMENT";
  case TT_ADD_CONCAT_OP:
    return "ADD_CONCAT_OP";
  case TT_ADD_CONDITION:
    return "ADD_CONDITION";
  case TT_ADD_ZERO_EXTENSION:
    return "ADD_ZERO_EXTENSION";
  case TT_ADD_SIGN_EXTENSION:
    return "ADD_SIGN_EXTENSION";
  case TT_ADD_DEF_UF:
    return "ADD_DEF_UF";
  case TT_ADD_UF_ARG:
    return "ADD_UF_ARG";
  case TT_ADD_UF_TERM_ARG:
    return "ADD_UF_TERM_ARG";
  case TT_ADD_LATCH:
    return "ADD_LATCH";
  case TT_ADD_UF_TERM:
    return "ADD_UF_TERM";
  case TT_ADD_ASSUMPTION:
    return "ADD_ASSUMPTION";
  case TT_TRUE:
    return "TRUE";
  case TT_FALSE:
    return "FALSE";
  case TT_NEQ:
    return "!=";
  case TT_CNF:
    return "cnf";
  case TT_QUOTED_STRING:
    return "QUOTED_STRING";
  case TT_GEQ:
    return ">=";
  case TT_LEQ:
    return "<=";
  case TT_ATTRIBUTE:
    return "<attribute>";
  case TT_ARITH:
    return "<arith>";
  case TT_USER:
    return "<user value>";
  }
  ASSERTION_VIOLATION;
} // Token::toString

}
