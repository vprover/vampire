/**
 * @file InputReader.cpp
 * Implements class InputReader.
 */

#include <string>
#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "TPTPLexer.hpp"
#include "TPTPParser.hpp"

#include "InputReader.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

UnitList* InputReader::getUnits()
{
  CALL("InputReader::getUnits");

  TimeCounter tc1(TC_PARSING);
  env.statistics->phase=Statistics::PARSING;


  string inputFile = env.options->inputFile();

  istream* input;
  if(inputFile=="") {
    input=&cin;
  } else {
    input=new ifstream(inputFile.c_str());
  }


  UnitList* units;
  switch (env.options->inputSyntax()) {
  case Options::IS_SIMPLIFY:
  {
    Shell::LispLexer lexer(*input);
    Shell::LispParser parser(lexer);
    LispParser::Expression* expr = parser.parse();
    SimplifyProver simplify;
    units = simplify.units(expr);
  }
  break;
  case Options::IS_TPTP:
  {
    TPTPLexer lexer(*input);
    TPTPParser parser(lexer);
    units = parser.units();
  }
  break;
  }

  if(inputFile!="") {
    delete static_cast<ifstream*>(input);
    input=0;
  }

  return units;

}

}
