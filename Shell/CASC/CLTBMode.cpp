/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

#include "CLTBMode.hpp"

namespace Shell
{
namespace CASC
{

using namespace std;

void CLTBMode::perform()
{
  CALL("CLTBMode::perform");

  readInput();
}

void CLTBMode::readInput()
{
  if(env.options->inputFile()=="") {
    USER_ERROR("Input file must be specified for cltb mode");
  }

  string line, word;
  ifstream in(env.options->inputFile().c_str());
  std::getline(in, line);
  if(line!="% SZS start BatchConfiguration") {
    USER_ERROR("\"% SZS start BatchConfiguration\" expected, \""+line+"\" found.");
  }

  in>>word;
  if(word!="division.category") {
    USER_ERROR("\"division.category\" expected, \""+word+"\" found.");
  }
  in>>division;

  in>>word;
  if(word!="limit.time.problem.wc") {
    USER_ERROR("\"limit.time.problem.wc\" expected, \""+word+"\" found.");
  }
  in>>problemTimeLimit;

  in>>word;
  if(word!="limit.time.overall.wc") {
    USER_ERROR("\"limit.time.overall.wc\" expected, \""+word+"\" found.");
  }
  in>>overallTimeLimit;

}

}
}
