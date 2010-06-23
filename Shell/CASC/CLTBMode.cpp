/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"

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

  cout<<division<<endl;
  cout<<problemTimeLimit<<endl;
  cout<<overallTimeLimit<<endl;
  StringList::Iterator iit(theoryIncludes);
  while(iit.hasNext()) {
    cout<<"\""<<iit.next()<<"\""<<endl;
  }
  StringPairStack::BottomFirstIterator prit(problemFiles);
  while(prit.hasNext()) {
    StringPair prb=prit.next();
    cout<<"'"<<prb.first<<"'  '"<<prb.second<<"'"<<endl;
  }
}

void CLTBMode::loadIncludes()
{
  CALL("CLTBMode::loadIncludes");

  theoryAxioms=0;

  StringList::Iterator iit(theoryIncludes);
  while(iit.hasNext()) {
    string fname=iit.next();
    ifstream inp(fname.c_str());
    TPTPLexer lexer(inp);
    TPTPParser parser(lexer);
    UnitList* funits = parser.units();
    if(parser.haveConjecture()) {
      USER_ERROR("Axiom file "+fname+" contains a conjecture.");
    }

    theoryAxioms=UnitList::concat(funits,theoryAxioms);
  }

  theorySelector.initSelectionStructure(theoryAxioms);
}

void CLTBMode::readInput()
{
  CALL("CLTBMode::readInput");

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

  std::getline(in, line);
  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchConfiguration") {
    USER_ERROR("\"% SZS end BatchConfiguration\" expected, \""+line+"\" found.");
  }
  std::getline(in, line);
  if(line!="% SZS start BatchIncludes") {
    USER_ERROR("\"% SZS start BatchIncludes\" expected, \""+line+"\" found.");
  }

  theoryIncludes=0;
  for(std::getline(in, line); line[0]!='%' && !in.eof(); std::getline(in, line)) {
    size_t first=line.find_first_of('\'');
    size_t last=line.find_last_of('\'');
    if(first==string::npos || first==last) {
      USER_ERROR("Include specification must contain the file name enclosed in the ' characters:\""+line+"\".");
    }
    ASS_G(last,first);
    string fname=line.substr(first+1, last-first-1);
    StringList::push(fname, theoryIncludes);
  }

  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchIncludes") {
    USER_ERROR("\"% SZS end BatchIncludes\" expected, \""+line+"\" found.");
  }
  std::getline(in, line);
  if(line!="% SZS start BatchProblems") {
    USER_ERROR("\"% SZS start BatchProblems\" expected, \""+line+"\" found.");
  }

  for(std::getline(in, line); line[0]!='%' && !in.eof(); std::getline(in, line)) {
    size_t spc=line.find(' ');
    size_t lastSpc=line.find(' ', spc+1);
    if(spc==string::npos || spc==0 || spc==line.length()-1) {
      USER_ERROR("Two file names separated by a single space expected:\""+line+"\".");
    }
    string inp=line.substr(0,spc);
    string outp=line.substr(spc+1, lastSpc-spc-1);
    problemFiles.push(make_pair(inp, outp));
  }

  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchProblems") {
    USER_ERROR("\"% SZS end BatchProblems\" expected, \""+line+"\" found.");
  }
}

}
}
