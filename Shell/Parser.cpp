/**
 * @file Parser.cpp
 * Implements class Parser
 *
 * @since 14/07/2004 Turku
 */

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"
#include "../Lib/Int.hpp"

#include "../Lib/IntNameTable.hpp"

#include "Lexer.hpp"
#include "Parser.hpp"

using namespace Lib;
using namespace Shell;

/**
 * Initialise a parser.
 * @since 17/07/2004 Helsinki Airport
 */
Parser::Parser (Lexer& lexer)
  :
  _lexer(lexer),
  _tokenCursor(0),
  _noOfTokens(0)
{
} // Parser::Parser


/**
 * Create a new parser exception.
 * @since 17/07/2004 Turku
 */
ParserException::ParserException (string message,const Token& token)
  : _message (message)
{
  _message += " in line ";
  _message += Int::toString(token.line);
  _message += " at ";
  _message += token.text;
} // ParserException::ParserException


/**
 * Write itself to an ostream.
 * @since 17/07/2004 Helsinki Airport
 */
void ParserException::cry (ostream& out)
{
  out << "Parser exception: " << _message << '\n';
} // ParserException::cry


/**
 * Read and consume a token of type tt. 
 * @throws ParserException if the next token has a wrong type.
 */
void Parser::consumeToken (TokenType tt)
{
  CALL("Parser::consumeToken/1");

  if (currentToken1().tag != tt) {
    throw ParserException(Token::toString(tt) + " expected",
			  _tokens[_tokenCursor]);
  }
  consumeToken();
} // Parser::consumeToken


/**
 * Check that the current token has type tt.
 * @throws ParserException if it has a wrong type.
 */
void Parser::expectToken (TokenType tt)
{
  CALL("Parser::expectToken");

  if (currentToken().tag != tt) {
    throw ParserException(Token::toString(tt) + " expected",
			  _tokens[_tokenCursor]);
  }
} // Parser::expectToken


/**
 * Move to the next token.
 * @since 15/07/2004 Turku
 */
void Parser::consumeToken ()
{
  CALL("Parser::consumeToken/0");

  ASS (_noOfTokens > 0);
  ASS (_tokenCursor < TOKEN_BUFFER_SIZE);

  _tokenCursor = (_tokenCursor+1) % TOKEN_BUFFER_SIZE;
  _noOfTokens--;
} // Parser::consumeToken()


/**
 * Read the next token. 
 * @since 15/07/2004 Turku, implemented as a Lexer method
 * @since 24/07/2004 Torrevieja
 */
void Parser::readToken ()
{
  CALL("Parser::readToken");

  ASS(_noOfTokens <= TOKEN_BUFFER_SIZE);

  if (_noOfTokens == TOKEN_BUFFER_SIZE) {
    _lexer.readToken(_tokens[0]);
    throw ParserException("token buffer capacity exceeded",_tokens[0]);
  }

  int tokenIndex = (_tokenCursor + _noOfTokens) % TOKEN_BUFFER_SIZE;
  _noOfTokens++;
  _lexer.readToken(_tokens[tokenIndex]);
} // Parser::readToken


/**
 * Return the current token.
 * @since 03/12/2006 Haifa
 */
Token& Parser::currentToken ()
{
  CALL("Parser::currentToken");
  ASS(_noOfTokens > 0);

  return _tokens[_tokenCursor % TOKEN_BUFFER_SIZE];
} // currentToken

/**
 * Read tokens up to the index token and return the lookahead token.
 *
 * @since 15/07/2004 Turku
 */
Token& Parser::lookAhead (int index)
{
  CALL("Parser::lookahead");

  ASS (index < TOKEN_BUFFER_SIZE);
  ASS(index > 0);

  while (_noOfTokens <= index) {
    readToken();
  }
  return _tokens[(_tokenCursor+index) % TOKEN_BUFFER_SIZE];
} // Parser::lookAhead()


/**
 * Convert the token text into a variable number. No check is made
 * whether the token type is TT_VAR.
 *
 * @since 26/07/2004 Torrevieja
 */
int Parser::var (const Token& t)
{
  CALL("Parser::var");
  return _vars.insert(t.text);
} // Parser::var


/**
 * Convert the token text into a double floating-point number. 
 * No check is made whether the token type is TT_REAL or TT_INTEGER.
 *
 * @since 02/08/2004 Torrevieja
 */
double Parser::real (const Token& token)
{
  CALL("Parser::real");
  double d;

  if (! Int::stringToDouble(token.text.c_str(),d)) {
    throw ParserException("incorrect floating point number",token);
  }
  return d;
} // Parser::real


/**
 * Convert the token text into an integer. 
 * No check is made whether the token type is TT_REAL or TT_INTEGER.
 *
 * @since 28/09/2004 Manchester
 */
int Parser::integer (const Token& token)
{
  CALL("Parser::integer");

  int result;
  if (Int::stringToInt(const_cast<string&>(token.text),result)) {
    return result;
  }
  throw ParserException("incorrect integer",token);
} // Parser::integer

/**
 * Convert the token text into a 64-bit unsigned.
 * No check is made whether the token type is TT_REAL or TT_INTEGER.
 *
 * @since 30/11/2006 Haifa
 */
long long unsigned Parser::unsigned64 (const Token& token)
{
  CALL("Parser:unsigned64");

  long long unsigned result;

  if (Int::stringToUnsigned64(const_cast<string&>(token.text),result)) {
    return result;
  }
  throw ParserException("incorrect 64-bit unsigned",token);
} // Parser::unsigned64


