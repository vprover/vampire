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
 * @file CParser.hpp
 * Defines class CParser for lexical analysis of C programs.
 *
 * @since 13/01/2011 Manchester
 */

#ifndef __CParser__
#define __CParser__

#include <vector>

#include "Lib/Exception.hpp"
#include "Lib/VString.hpp"

using namespace std;

namespace Shell {

/**
 * Class CParser, implements a C language parser.
 * @since 13/01/2011 Manchester
 */
class CParser 
{
public:
  /**
   * Implements lexer exceptions.
   * @since 14/01/2011 Manchester
   */
  class LexerException 
    : public Lib::Exception
  {
  public:                                
    LexerException(const CParser&,unsigned pos,Lib::vstring message);
    void cry(ostream&) const override;
    ~LexerException() {}
  protected:
    Lib::vstring _message;
    unsigned _pos;
  }; // CParser::LexerException

  /**
   * Implements parser exceptions.
   * @since 17/01/2011 Manchester
   */
  class ParserException 
    : public Lib::Exception
  {
  public:                                
    ParserException(const CParser&,unsigned pos,Lib::vstring message);
    void cry(ostream&) const override;
    ~ParserException() {}
  protected:
    Lib::vstring _message;
    unsigned _pos;
  }; // CParser::ParserException

  /** lexer token types */
  enum LTType {
    /** identifier */
    LT_IDENTIFIER,

    /** keyword auto */
    LT_AUTO,
    /** keyword break */
    LT_BREAK,
    /** keyword case */
    LT_CASE,
    /** keyword char */
    LT_CHAR,
    /** keyword const */
    LT_CONST,
    /** keyword continue */
    LT_CONTINUE,
    /** keyword default */
    LT_DEFAULT,
    /** keyword do */
    LT_DO,
    /** keyword double */
    LT_DOUBLE,
    /** keyword else */
    LT_ELSE,
    /** keyword enum */
    LT_ENUM,
    /** keyword extern */
    LT_EXTERN,
    /** keyword float */
    LT_FLOAT,
    /** keyword for */
    LT_FOR,
    /** keyword goto */
    LT_GOTO,
    /** keyword if */
    LT_IF,
    /** keyword inline */
    LT_INLINE,
    /** keyword int */
    LT_INT,
    /** keyword long */
    LT_LONG,
    /** keyword register */
    LT_REGISTER,
    /** keyword restrict */
    LT_RESTRICT,
    /** keyword return */
    LT_RETURN,
    /** keyword short */
    LT_SHORT,
    /** keyword signed */
    LT_SIGNED,
    /** keyword sizeof */
    LT_SIZEOF,
    /** keyword struct */
    LT_STRUCT,
    /** keyword switch */
    LT_SWITCH,
    /** keyword typedef */
    LT_TYPEDEF,
    /** keyword union */
    LT_UNION,
    /** keyword unsigned */
    LT_UNSIGNED,
    /** keyword void */
    LT_VOID,
    /** keyword volatile */
    LT_VOLATILE,
    /** keyword while */
    LT_WHILE,

    /** { */
    LT_LBRACE,
    /** } */
    LT_RBRACE,
    /** { */
    LT_LPAR,
    /** } */
    LT_RPAR,
    /** ; */
    LT_SEMICOLON,
    /** == */
    LT_EQ_OP,
    /** = */
    LT_ASSIGN,
    /** += */
    LT_ADD_ASSIGN,
    /** ++ */
    LT_INC_OP,
    /** + */
    LT_ADD,
    /** *= */
    LT_MULT_ASSIGN,
    /** * */
    LT_MULT,
    /** ... */
    LT_ELLIPSIS,
    /** dot */
    LT_DOT,
    /** >= */
    LT_GE_OP,
    /** > */
    LT_GREATER,
    /** >>= */
    LT_RIGHT_ASSIGN,
    /** >> */
    LT_RIGHT_OP,
    /** <= */
    LT_LE_OP,
    /** [ */
    LT_LBRACKET,
    /** < */
    LT_LESS,
    /** <<= */
    LT_LEFT_ASSIGN,
    /** << */
    LT_LEFT_OP,
    /** -= */
    LT_SUB_ASSIGN,
    /** -- */
    LT_DEC_OP,
    /** -> */
    LT_PTR_OP,
    /** - */
    LT_MINUS,
    /** /= */
    LT_DIV_ASSIGN,
    /** / */
    LT_DIV,
    /** %= */
    LT_MOD_ASSIGN,
    /** % */
    LT_MOD,
    /** &= */
    LT_AND_ASSIGN,
    /** && */
    LT_AND_OP,
    /** & */
    LT_AMP,
    /** |= */
    LT_OR_ASSIGN,
    /** || */
    LT_OR_OP,
    /** | */
    LT_BAR,
    /** ^= */
    LT_XOR_ASSIGN,
    /** ^ */
    LT_XOR,
    /** != */
    LT_NE_OP,
    /** ! */
    LT_EXCLAMATION,
    /** : */
    LT_COLON,
    /** ] */
    LT_RBRACKET,
    /** , */
    LT_COMMA,
    /** ~ */
    LT_TILDE,
    /** ? */
    LT_QUESTION,

    /** an integer constant */
    LT_INT_CONST,
    /** a long constant */
    LT_LONG_CONST,
    /** an unsigned integer constant */
    LT_UINT_CONST,
    /** an unsigned long constant */
    LT_ULONG_CONST,
    /** a floating point constant */
    LT_FLOAT_CONST,
    /** a double floating point constant */
    LT_DOUBLE_CONST,
    /** a string constant */
    LT_STRING_CONST,
    /** a character constant */
    LT_CHAR_CONST,
    /** end-of-input */
    LT_EOF,
  };

  struct Token {
    LTType type;
    unsigned start;
    unsigned end;
  };

  /** parser token types */
  enum PTType {
    /** constant expression */
    PT_CONSTANT_EXPRESSION,
    /** array application */
    PT_ARRAY_APPLICATION,
    /** identifier */
    PT_IDENTIFIER,
  };

  /** the base class for all parsed expressions */
  class Unit {
  public:
    /** the parser type of this unit */
    PTType type() const { return _type; }
    /** create a new unit of a given type */
    Unit(PTType tp,unsigned start,unsigned end)
      : _type(tp), _start(start), _end(end)
    {}
    /** the start position of the unit in the array of tokens */
    unsigned start() const { return _start; }
    /** the end position of the unit in the array of tokens */
    unsigned end() const { return _end; }
  protected:
    /** unit type */
    PTType _type;
    /** start position in the array of tokens */
    unsigned _start;
    /** end position in the array of tokens */
    unsigned _end;
  };

  /** constant expression */
  class ConstantExpression
    : public Unit
  {
  public:
    /** create a new constant expression */
    ConstantExpression(unsigned start,unsigned end);
  };

  /** identifier */
  class Identifier
    : public Unit
  {
  public:
    /** create a new identifier */
    Identifier(unsigned start,unsigned end);
  };

  /** identifier */
  class ArrayApplication
    : public Unit
  {
  public:
    /** create a new array application expression */
    ArrayApplication(unsigned start,unsigned end,Unit* lhs,Unit* rhs):
      Unit(PT_ARRAY_APPLICATION,start,end)
    {}
  };

  CParser(const char* input);
  ~CParser();
  void tokenize();
  /** return the input string */
  const char* input() const { return _input; }

  #if VDEBUG
  void output(ostream& str);
  static const char* toString(LTType);
  #endif

private:
  // Lexer procedures
  unsigned skipWhiteSpacesAndComments(unsigned pos);
  unsigned skipToEndOfLine(unsigned pos);
  unsigned skipToEndOfComment(unsigned pos);

  LTType keyword(unsigned pos,unsigned end);
  static bool keyword(const char* txt,const char* word,int chars);

  unsigned integerTypeSuffix(unsigned start,LTType&);
  unsigned decimalLiteral(unsigned start,LTType&);
  unsigned octalLiteral(unsigned start,LTType&);
  unsigned hexLiteral(unsigned start,LTType&);
  unsigned floatingPointLiteral(unsigned start,LTType&);
  unsigned exponent(unsigned start);
  unsigned identifier(unsigned start);
  unsigned numericConstant(unsigned start,LTType&);
  unsigned stringConstant(unsigned start);
  unsigned charConstant(unsigned start);

  /** true if c is a digit 0-9 */
  static bool digit(char c) { return c >= '0' && c <= '9'; }
  static bool letter(char c);
  static bool floatTypeSuffix(char c,LTType&);
  static bool hexDigit(char c);

  // parser procedures
  unsigned primaryExpression(unsigned pos,bool backtrack);
  unsigned postfixExpression(unsigned pos,bool backtrack);
  unsigned unaryExpression(unsigned pos,bool backtrack);
  unsigned multiplicativeExpression(unsigned pos,bool backtrack);
  unsigned additiveExpression(unsigned pos,bool backtrack);
  unsigned shiftExpression(unsigned pos,bool backtrack);
  unsigned relationalExpression(unsigned pos,bool backtrack);
  unsigned equalityExpression(unsigned pos,bool backtrack);
  unsigned andExpression(unsigned pos,bool backtrack);
  unsigned xorExpression(unsigned pos,bool backtrack);
  unsigned orExpression(unsigned pos,bool backtrack);
  unsigned logicalAndExpression(unsigned pos,bool backtrack);
  unsigned logicalOrExpression(unsigned pos,bool backtrack);
  unsigned conditionalExpression(unsigned pos,bool backtrack);
  unsigned assignmentExpression(unsigned pos,bool backtrack);
  unsigned expression(unsigned pos,bool backtrack);
  bool consumeToken(LTType t,unsigned pos,bool backtrack);
  unsigned argumentExpressionList(unsigned pos,bool backtrack);

  /** the input string, must be null-terminated */
  const char* _input;
  /** the collected list of tokens */
  vector<Token> _tokens;
  /** the collected list of parsed units */
  vector<Unit*> _units;
}; // class CParser

}

#endif

