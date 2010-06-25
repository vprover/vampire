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

#include "CASCMode.hpp"

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
  loadIncludes();

  StringPairStack::BottomFirstIterator probs(problemFiles);
  while(probs.hasNext()) {
    StringPair res=probs.next();

    string probFile=res.first;
    string outFile=res.second;

    pid_t child=Multiprocessing::instance()->fork();
    if(!child) {
      CLTBProblem prob(this, probFile, outFile);
      prob.perform();

      //the prob.perform() function should never return
      ASSERTION_VIOLATION;
    }

    int resValue;
    pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
    ASS_EQ(finishedChild, child);
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

  //fork off the writer child process
  writerChildPid=Multiprocessing::instance()->fork();
  if(!writerChildPid) {
    runWriterChild();
  }

  //only the writer child is reading from the pipe (and it is now forked off)
  childOutputPipe.neverRead();
}

CLTBProblem::~CLTBProblem()
{
  CALL("CLTBProblem::~CLTBProblem");

  //We're finishing, so we'll never write to the pipe again.
  childOutputPipe.neverWrite();

  //The above should made the writer child terminate.
  int resValue;
  pid_t lastChild=Multiprocessing::instance()->waitForChildTermination(resValue);
  ASS_EQ(lastChild, writerChildPid);
  ASS_EQ(resValue,0);
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

  runSchedule(quick);

  _exit(1); //we didn't find the proof, so we return nonzero status code
}

/**
 * Run schedule in @b sliceCodes. Terminate the process with 0 exit status
 * if proof was found, otherwise return false.
 */
bool CLTBProblem::runSchedule(const char** sliceCodes)
{
  CALL("CLTBProblem::runSchedule");

  NOT_IMPLEMENTED;

  int parallelProcesses=System::getNumberOfCores();
  int processesLeft=parallelProcesses;

  const char** nextSlice=sliceCodes;

  while(*nextSlice) {
    while(*nextSlice && processesLeft) {
      ASS_G(processesLeft,0);

      int remainingTime = env.remainingTime()/100;
      if(remainingTime<=0) {
        return false;
      }
      int sliceTime = getSliceTime(*nextSlice);
      if(sliceTime>remainingTime) {
	sliceTime=remainingTime;
      }


      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if(!childId) {
        //we're in a proving child
        env.setPipeOutput(&childOutputPipe); //direct output into the pipe
        runChild(*nextSlice, sliceTime); //start proving
      }

#if VDEBUG
      ALWAYS(childIds.insert(childId));
#endif

      nextSlice++;
      processesLeft--;
    }

    waitForChildAndExitWhenProofFound();
    processesLeft++;
  }

  while(parallelProcesses!=processesLeft) {
    waitForChildAndExitWhenProofFound();
  }
  return false;
}

/**
 * Wait for termination of a child and terminate the process with a zero status
 * if a proof was found. If the child didn't find the proof, just return.
 */
void CLTBProblem::waitForChildAndExitWhenProofFound()
{
  CALL("CLTBProblem::waitForChildAndExitWhenProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if(!resValue) {
    //we have found the proof. It has been already written down by the writter child,
    //so we can just terminate
    _exit(0);
  }
}

/**
 * Read everything from the pipe and write it into the output file.
 * Terminate after all writing ends of the pipe are closed.
 *
 * This function is to be run in a forked-off process
 */
void CLTBProblem::runWriterChild()
{
  CALL("CLTBProblem::runWriterChild");

  //we're in the child that writes down the output of other children
  childOutputPipe.neverWrite();

  ofstream out(outFile.c_str());

  childOutputPipe.acquireRead();

  while(!childOutputPipe.in().eof()) {
    string line;
    getline(childOutputPipe.in(), line);
    out<<line;
  }

  childOutputPipe.releaseRead();
  _exit(0);
}

void CLTBProblem::runChild(string slice, unsigned ds)
{
  CALL("CLTBProblem::runChild");

  Options opt=*env.options;
  opt.readFromTestId(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if(stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  runChild(opt);
}

/**
 * Do the theorem proving in a forked-off process
 */
void CLTBProblem::runChild(Options& opt)
{
  CALL("CLTBProblem::runChild");

  UIHelper::cascModeChild=true;
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  *env.options=opt;
  //we have already performed the normalization
  env.options->setNormalize(false);

  if(env.options->sineSelection()!=Options::SS_OFF) {
    //add selected axioms from the theory
    parent->theorySelector.addSelectedAxioms(probUnits);

    env.options->setSineSelection(Options::SS_OFF);
  }
  else {
    //if there wasn't any sine selection, just put in all theory axioms
    probUnits=UnitList::concat(probUnits, parent->theoryAxioms);
  }

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

/**
 * Return intended slice time in deciseconds
 */
unsigned CLTBProblem::getSliceTime(string sliceCode)
{
  CALL("CLTBProblem::getSliceTime");

  string sliceTimeStr=sliceCode.substr(sliceCode.find_last_of('_')+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr, sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = (unsigned)(sliceTime * SLOWNESS) + 1;
  if (time < 10) {
    time++;
  }
  return time;
}


}
}
