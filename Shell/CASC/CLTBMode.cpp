/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 */

#include <fstream>
#include <cstdlib>
#include <csignal>

//#include "Lib/Portability.hpp"

//#if !COMPILER_MSVC
//#include <unistd.h>
//#endif

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
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

/**
 * This function runs the batch master process and spawns the child master processes
 *
 * In this function we:
 * 1) read the batch file
 * 2) load the common axioms and put them into a SInE selector
 * 3) run a child master process for each problem (sequantially)
 */
void CLTBMode::perform()
{
  CALL("CLTBMode::perform");

  readInput();
  env.options->setTimeLimitInSeconds(overallTimeLimit);

  loadIncludes();

  int solvedCnt=0;

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
    env.beginOutput();
    env.out()<<"% SZS status Started for "<<probFile<<endl;
    env.out()<<"solver pid "<<child<<endl;
    env.endOutput();
    int resValue;
    pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);
    ASS_EQ(finishedChild, child);

    env.beginOutput();
    if(!resValue) {
      env.out()<<"% SZS status Theorem for "<<probFile<<endl;
      solvedCnt++;
    }
    else {
      env.out()<<"% SZS status GaveUp for "<<probFile<<endl;
    }
    env.out()<<"% SZS status Ended for "<<probFile<<endl;
    env.endOutput();

    Timer::syncClock();
  }
  env.beginOutput();
  env.out()<<"Solved "<<solvedCnt<<" out of "<<problemFiles.size()<<endl;
  env.endOutput();
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
  in>>category;

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
}

/**
 * This function should use the runSchedule function to prove the problem.
 * Once the problem is proved, the @b runSchedule function does not return
 * and the process terminates.
 *
 * The properties of the problem are in the @b property field.
 * The name of problem category (MZR, SMO or CYC) is in @b parent->category.
 *
 * If a slice contains sine_selection value different from off, theory axioms
 * will be selected using SInE from the common axioms included in the batch file
 * (all problem axioms, including the included ones, will be used as a base
 * for this selection).
 *
 * If the sine_selection is off, all the common axioms will be just added to the
 * problem axioms. All this is done in the @b runChild(Options&) function.
 */
void CLTBProblem::performStrategy()
{
  CALL("CLTBProblem::performStrategy");

  const char* quick[] = {
//      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_379",
//      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_144",
//      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_557",
//      "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_382",
//      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_359",
      "lrs+11_5_cond=fast:fde=none:nwc=2.5:ptb=off:ss=included:sgo=on:spl=backtracking_35",
      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_37",
      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_14",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_35",
      "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_38",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_35",
      0
  };

  runSchedule(quick);

}


void CLTBProblem::perform()
{
  CALL("CLTBProblem::perform");

  System::registerForSIGHUPOnParentDeath();

  env.timer->reset();
  env.timer->start();
  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  env.options->setTimeLimitInSeconds(parent->problemTimeLimit);
  env.options->setInputFile(problemFile);

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

  //now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  //fork off the writer child process
  writerChildPid=Multiprocessing::instance()->fork();
  if(!writerChildPid) {
    runWriterChild();
    ASSERTION_VIOLATION; // the runWriterChild() function should never return
  }
  cout<<"writer pid "<<writerChildPid<<endl;
  cout.flush();

  //when the pipe will be closed, we want the process to terminate properly
  signal(SIGPIPE, &terminatingSignalHandler);

  //only the writer child is reading from the pipe (and it is now forked off)
  childOutputPipe.neverRead();

  env.setPipeOutput(&childOutputPipe); //direct output into the pipe
  UIHelper::cascMode=true;

  performStrategy();

  exitOnNoSuccess();
  ASSERTION_VIOLATION; //the exitOnNoSuccess() function should never return
}

/**
 * This function exits the problem master process if the problem
 * was not solved
 *
 * The unsuccessful problem master process does not have to
 * necessarily call this function to exit.
 */
void CLTBProblem::exitOnNoSuccess()
{
  CALL("CLTBProblem::exitOnNoSuccess");

  env.beginOutput();
  env.out()<<"% Proof not found in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
  if(env.remainingTime()/100>0) {
    env.out()<<"% SZS status GaveUp for "<<env.options->problemName()<<endl;
  }
  else {
    //From time to time we may also be terminating in the timeLimitReached()
    //function in Lib/Timer.cpp in case the time runs out. We, however, output
    //the same string there as well.
    env.out()<<"% SZS status Timeout for "<<env.options->problemName()<<endl;
  }
  env.endOutput();

  env.setPipeOutput(0);
  //This should make the writer child terminate.
  childOutputPipe.neverWrite();

  int resValue;
  pid_t lastChild=Multiprocessing::instance()->waitForChildTermination(resValue);
  ASS_EQ(lastChild, writerChildPid);
  ASS_EQ(resValue,0);


  cout<<"terminated solver pid "<<getpid()<<" (fail)"<<endl;
  cout.flush();

  System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
}

/**
 * Run schedule in @b sliceCodes. Terminate the process with 0 exit status
 * if proof was found, otherwise return false.
 */
bool CLTBProblem::runSchedule(const char** sliceCodes)
{
  CALL("CLTBProblem::runSchedule");

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
        runChild(*nextSlice, sliceTime); //start proving

        ASSERTION_VIOLATION; //the runChild function should never return
      }
      Timer::syncClock();

#if VDEBUG
      ALWAYS(childIds.insert(childId));
#endif

      cout<<"slice pid "<<childId<<" slice: "<<(*nextSlice)<<" time: "<<sliceTime<<endl;
      cout.flush();


      nextSlice++;
      processesLeft--;
    }

    if(processesLeft==0) {
      waitForChildAndExitWhenProofFound();
      processesLeft++;
    }
  }

  while(parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    waitForChildAndExitWhenProofFound();
    processesLeft++;
    Timer::syncClock();
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
    cout<<"terminated slice pid "<<finishedChild<<" (success)"<<endl;
    cout.flush();
    System::terminateImmediately(0);
  }
  cout<<"terminated slice pid "<<finishedChild<<" (fail)"<<endl;
  cout.flush();
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

  System::registerForSIGHUPOnParentDeath();
  signal(SIGHUP, &terminatingSignalHandler);
  Timer::setTimeLimitEnforcement(false);

  //we're in the child that writes down the output of other children
  childOutputPipe.neverWrite();

  ofstream out(outFile.c_str());

  childOutputPipe.acquireRead();

  while(!childOutputPipe.in().eof()) {
    string line;
    getline(childOutputPipe.in(), line);
    out<<line<<endl;
  }
  out.close();

  childOutputPipe.releaseRead();

  System::terminateImmediately(0);
}

void CLTBProblem::terminatingSignalHandler(int sigNum)
{
  System::terminateImmediately(0);
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

  System::registerForSIGHUPOnParentDeath();

  UIHelper::cascModeChild=true;

  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();
  Timer::setTimeLimitEnforcement(true);

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
