/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>
#include <cstdlib>

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/UIHelper.hpp"

#include "CLTBMode.hpp"

namespace Shell
{
namespace CASC
{

using namespace std;
using namespace Lib;
using namespace Lib::Sys;

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

  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

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
  }

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::PROPERTY_SCANNING;

    property.scan(theoryAxioms);
  }

  {
    TimeCounter tc(TC_SINE_SELECTION);
    env.statistics->phase=Statistics::SINE_SELECTION;

    theorySelector.initSelectionStructure(theoryAxioms);
  }
  env.statistics->phase=Statistics::UNKNOWN_PHASE;
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


//////////////////////////////////////////
// CLTBProblem
//////////////////////////////////////////

CLTBProblem::CLTBProblem(CLTBMode* parent, string problemFile, string outFile)
: parent(parent), problemFile(problemFile), outFile(outFile), property(parent->property)
{
  CALL("CLTBProblem::CLTBProblem");

  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    ifstream inp(problemFile.c_str());
    TPTPLexer lexer(inp);
    TPTPParser parser(lexer);
    parser.setForbiddenIncludes(parent->theoryIncludes);

    probUnits = parser.units();
    UIHelper::setConjecturePresence(parser.haveConjecture());
  }

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::PROPERTY_SCANNING;

    property.scan(probUnits);

    env.statistics->phase=Statistics::NORMALIZATION;

    Normalisation norm;
    probUnits = norm.normalise(probUnits);
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;
}

void CLTBProblem::perform()
{
  CALL("CLTBProblem::perform");

  env.options->setTimeLimitInSeconds(parent->problemTimeLimit);

  const char* quick[] = {
      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_379",
      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_144",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_557",
      "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_382",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_359",
      0
  };

}

bool CLTBProblem::runSchedule(const char** sliceCodes, unsigned ds)
{
  CALL("CLTBProblem::runSchedule");

  NOT_IMPLEMENTED;

  int parallelProcesses=System::getNumberOfCores();
  int processesLeft=parallelProcesses;

  DHSet<pid_t> childIds;
}

/**
 * Do the theorem proving in a forked-off process
 */
void CLTBProblem::childRun(Options& opt)
{
  CALL("CLTBProblem::childRun");

  UIHelper::cascModeChild=true;
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  *env.options=opt;
  //we have already performed the normalization
  env.options->setNormalize(false);
  env.options->setSineSelection(Options::SS_OFF);

  env.beginOutput();
  env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  UIHelper::runVampire(probUnits, &property);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  exit(resultValue);
}


}
}
