/**
 * @file CMZRMode.cpp
 * Implements class CMZRMode.
 */

#include <fstream>
#include <cstdlib>
#include <csignal>
#include <sstream>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/StringUtils.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "CASCMode.hpp"

#include "CMZRMode.hpp"

#define SLOWNESS 1.15

using namespace Shell::CASC;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

CMZRMode::CMZRMode()
{
  CALL("CMZRMode::CMZRMode");

#if __APPLE__
  //the core retrieval on mac is not implemented yet, hence this quick hack
  unsigned coreNumber = 2;
#else
  unsigned coreNumber = System::getNumberOfCores();
#endif
  if(coreNumber<=1) {
    _parallelProcesses = 1;
  }
  else if(coreNumber>=8) {
    _parallelProcesses = coreNumber-2;
  }
  else {
    _parallelProcesses = coreNumber-1;
  }
  _availCoreCnt = _parallelProcesses;
}

void CMZRMode::perform()
{
  CALL("CMZRMode::perform");

  UIHelper::cascMode = true;

  if(env.options->inputFile()=="") {
    USER_ERROR("Input file must be specified for CMZR mode");
  }

  string line;
  ifstream in(env.options->inputFile().c_str());
  if(in.fail()) {
    USER_ERROR("Cannot open input file: "+env.options->inputFile());
  }

  //support several batches in one file
  while(!in.eof()) {
    stringstream singleInst;
    bool ready = false;
    while(!in.eof()) {
      std::getline(in, line);
      singleInst<<line<<endl;
      if(line=="% SZS end BatchProblems") {
	ready = true;
	break;
      }
    }
    if(!ready) { break; }
    Shell::CASC::CMZRMode ltbm;
    stringstream childInp(singleInst.str());
    ltbm.perform(childInp);
  }
}

void CMZRMode::loadProblems()
{
  CALL("CMZRMode::loadProblems");

  Stack<ProblemInfo>::DelIterator pit(_problems);
  while(pit.hasNext()) {
    ProblemInfo& pi = pit.next();

    string fname = pi.inputFName;
    cout<<"% SZS status Started for "<<fname<<endl;;

    ifstream inp(fname.c_str());
    if(inp.fail()) {
      USER_ERROR("Cannot open problem file: "+fname);
    }
    Parse::TPTP parser(inp);

    List<string>::Iterator iit(theoryIncludes);
    while (iit.hasNext()) {
      parser.addForbiddenInclude(iit.next());
    }

    parser.parse();

    pi.specificFormulas = parser.units();
    pi.hasConjecture = parser.containsConjecture();
    pi.property = new Property(*_axiomProperty);
    pi.property->add(pi.specificFormulas);

    getStrategy(*pi.property, pi.schedule);

    ofstream outFile(pi.outputFName.c_str());
    outFile << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!"<<endl;
    outFile.close();
  }
}

void CMZRMode::attemptProblem(unsigned idx)
{
  CALL("CMZRMode::attemptProblem");
  ASS_G(_availCoreCnt,0);

  string strategy = _problems[idx].schedule.pop();
  unsigned timeMs = getSliceTime(strategy);
  LOG("bug","planned: "<<timeMs);

  if(env.remainingTime()*_parallelProcesses<timeMs*_unsolvedCnt) {
    timeMs = (env.remainingTime()*_parallelProcesses)/_unsolvedCnt;
    LOG("bug","proportional: "<<timeMs);
  }
  if(env.remainingTime()<timeMs) {
    timeMs = env.remainingTime();
    LOG("bug","safe: "<<timeMs);
  }

  startStrategyRun(idx, strategy,timeMs);
  if(_availCoreCnt==0) {
    waitForOneFinished();
  }
}

void CMZRMode::waitForOneFinished()
{
  CALL("CMZRMode::waitForOneFinished");
  ASS(!_processProblems.isEmpty());
  ASS_G(_unsolvedCnt,0);

  ProcessMap::Iterator pit(_processProblems);
  while(pit.hasNext()) {
    unsigned prbIdx = pit.next();
    const ProblemInfo& pi = _problems[prbIdx];
    ASS_NEQ(pi.runningProcessPID,-1);
    if(pi.processDueTime<env.timer->elapsedMilliseconds()) {
      cout<<"killed overdue pid "<<pi.runningProcessPID<<" at "<<env.timer->elapsedMilliseconds()<<" ms"<<endl;
      kill(pi.runningProcessPID,SIGKILL);
    }
  }

  int resValue;
  pid_t finishedChild=Multiprocessing::instance()->waitForChildTermination(resValue);

  unsigned prbIdx = _processProblems.get(finishedChild);
  _processProblems.remove(finishedChild);
  _availCoreCnt++;

  ProblemInfo& pi = _problems[prbIdx];
  pi.runningProcessPID = -1;
  if(!resValue) {
    pi.solved = true;
    _unsolvedCnt--;
    cout<<"terminated slice pid "<<finishedChild<<" on "<<pi.inputFName<<" (success) at "<<env.timer->elapsedMilliseconds()<<" ms"<<endl;
    cout<<"% SZS status Theorem for "<<pi.inputFName<<endl;
    cout<<"% SZS status Ended for "<<pi.inputFName<<endl;
  }

  cout<<"terminated slice pid "<<finishedChild<<" on "<<pi.inputFName<<" (fail) at "<<env.timer->elapsedMilliseconds()<<" ms"<<endl;
  cout.flush();
}

void CMZRMode::startStrategyRun(unsigned prbIdx, string strategy, unsigned timeMs)
{
  CALL("CMZRMode::startStrategyRun");
  ASS_G(_availCoreCnt,0);

  _availCoreCnt--;

  pid_t childId=Multiprocessing::instance()->fork();
  ASS_NEQ(childId,-1);
  if(!childId) {
    //we're in a proving child
    strategyRunChild(prbIdx,strategy, timeMs); //start proving
    ASSERTION_VIOLATION; //the runChild function should never return
  }
  Timer::syncClock();

  ALWAYS(_processProblems.insert(childId, prbIdx));
  _problems[prbIdx].runningProcessPID = childId;
  _problems[prbIdx].processDueTime = env.timer->elapsedMilliseconds()+timeMs+100;

  cout<<"started slice pid "<<childId<<" "<<strategy<<" on "<<_problems[prbIdx].inputFName
      <<" for "<<timeMs<<" ms"<<endl;
}

void CMZRMode::strategyRunChild(unsigned prbIdx, string strategy, unsigned timeMs)
{
  CALL("CMZRMode::strategyRunChild");

  Timer::setTimeLimitEnforcement(true);
  UIHelper::cascModeChild=true;

  ProblemInfo& pi = _problems[prbIdx];
  ofstream outFile(pi.outputFName.c_str(), ios_base::app);
  env.setPriorityOutput(&outFile);

  Options opt=*env.options;
  opt.readFromTestId(strategy);

  unsigned dsTime = timeMs/100;
  if(dsTime==0) {
    dsTime = 1;
  }
  opt.setTimeLimitInDeciseconds(dsTime);
  int stl = opt.simulatedTimeLimit();
  if(stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }

  System::registerForSIGHUPOnParentDeath();


  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  //we have already performed the normalization
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  //here we make the strategy options drive vampire, particularly
  //we replace the global time limit by the strategy time limit.
  *env.options = opt;

  env.beginOutput();
  env.out()<<opt.testId()<<" on "<<opt.problemName()<<" for "<<env.remainingTime()<<" ms"<<endl;
  env.endOutput();

  UIHelper::setConjecturePresence(pi.hasConjecture);

  baseProblem->addUnits(pi.specificFormulas);
  ProvingHelper::runVampire(*baseProblem, opt);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  env.setPriorityOutput(0);
  outFile.close();

  exit(resultValue);
}

bool CMZRMode::canAttemptProblem(unsigned idx) const
{
  CALL("CMZRMode::canAttemptProblem");

  const ProblemInfo& pi = _problems[idx];
  return !pi.solved && pi.runningProcessPID==-1 && pi.schedule.isNonEmpty();
}

/**
 * This function runs the batch master process and spawns the child master processes
 *
 * In this function we:
 * 1) read the batch file
 * 2) load the common axioms and put them into a SInE selector
 * 3) run a child master process for each problem (sequentially)
 */
void CMZRMode::perform(istream& batchFile)
{
  CALL("CMZRMode::perform");

  readInput(batchFile);

  bool noProblemLimit = false;
  if(problemTimeLimit==0) {
    //problem time is unlimited, we need to keep updating it based on the overall
    //limit and remaining problems
    noProblemLimit = true;
  }
  else {
    //we have a problem time limit, so we don't use the overall limit
//  env.options->setTimeLimitInSeconds(overallTimeLimit);
    env.options->setTimeLimitInSeconds(0);
  }

  loadIncludes();
  loadProblems();

  Timer::setTimeLimitEnforcement(false);

  unsigned prbCnt = _problems.size();
  _unsolvedCnt = prbCnt;
  unsigned nextProblemIdx = 0;
  for(;;) {
    if(env.timeLimitReached()) {
      break;
    }
    unsigned startIdx = nextProblemIdx;
    while(_problems[nextProblemIdx].solved || _problems[nextProblemIdx].runningProcessPID!=-1) {
      nextProblemIdx = (nextProblemIdx+1)%prbCnt;
      if(nextProblemIdx==startIdx) {
	if(_processProblems.isEmpty()) {
	  goto fin;
	}
	waitForOneFinished();
      }
    }
    attemptProblem(nextProblemIdx);
    nextProblemIdx = (nextProblemIdx+1)%prbCnt;
  }

fin:

  for(unsigned i=0; i<prbCnt; i++) {
    ProblemInfo& pi = _problems[i];

    if(pi.runningProcessPID==-1) {
      continue;
    }
    kill(pi.runningProcessPID,SIGKILL);
    cout << "Kiling child "<<pi.runningProcessPID<<endl;
  }

  while(!_processProblems.isEmpty()) {
    waitForOneFinished();
  }

  for(unsigned i=0; i<prbCnt; i++) {
    ProblemInfo& pi = _problems[i];

    if(pi.solved) {
      continue;
    }
    ofstream outFile(pi.outputFName.c_str(), ios_base::app);
    outFile<<"% SZS status Timeout for "<<pi.inputFName<<endl;
    cout<<"% SZS status Ended for "<<pi.inputFName<<endl;
  }

  unsigned solvedCnt = prbCnt - _unsolvedCnt;
  cout<<"Solved "<<solvedCnt<<" out of "<<prbCnt<<" in "<<env.timer->elapsedMilliseconds()<<" ms"<<endl;
}

void CMZRMode::loadIncludes()
{
  CALL("CMZRMode::loadIncludes");

  UnitList* theoryAxioms=0;
  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    StringList::Iterator iit(theoryIncludes);
    while(iit.hasNext()) {
      string fname=env.options->includeFileName(iit.next());
      ifstream inp(fname.c_str());
      if(inp.fail()) {
        USER_ERROR("Cannot open included file: "+fname);
      }
      Parse::TPTP parser(inp);
      parser.parse();
      UnitList* funits = parser.units();
      if(parser.containsConjecture()) {
	USER_ERROR("Axiom file "+fname+" contains a conjecture.");
      }

      UnitList::Iterator fuit(funits);
      while(fuit.hasNext()) {
	fuit.next()->markIncluded();
      }
      theoryAxioms=UnitList::concat(funits,theoryAxioms);
    }
  }

  baseProblem = new Problem(theoryAxioms);

  //ensure we scan the theory axioms for property here, so we don't need to
  //do it afterward in each problem

  _axiomProperty = new Property(*baseProblem->getProperty());

  env.statistics->phase=Statistics::UNKNOWN_PHASE;
}

void CMZRMode::readInput(istream& in)
{
  CALL("CMZRMode::readInput");

  string line, word;

  std::getline(in, line);
  if(line!="% SZS start BatchConfiguration") {
    USER_ERROR("\"% SZS start BatchConfiguration\" expected, \""+line+"\" found.");
  }

  std::getline(in, line);

  questionAnswering = false;
  problemTimeLimit = -1;
  category = "";

  StringStack lineSegments;
  while(!in.eof() && line!="% SZS end BatchConfiguration") {
    lineSegments.reset();
    StringUtils::splitStr(line.c_str(), ' ', lineSegments);
    string param = lineSegments[0];
    if(param=="division.category") {
      if(lineSegments.size()!=2) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }
      category = lineSegments[1];
      LOG("ltb_conf","ltb_conf: "<<param<<" = "<<category);
    }
    else if(param=="output.required" || param=="output.desired") {
      if(lineSegments.find("Answer")) {
	questionAnswering = true;
	LOG("ltb_conf","ltb_conf: enabled question answering");
      }
    }
    else if(param=="execution.order") {
      //we ignore this for now and always execute in order
    }
    else if(param=="limit.time.problem.wc") {
      if(lineSegments.size()!=2 || !Int::stringToInt(lineSegments[1], problemTimeLimit)) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }
      LOG("ltb_conf","ltb_conf: "<<param<<" = "<<problemTimeLimit);
    }
    else {
      USER_ERROR("unknown batch configuration parameter: \""+line+"\"");
    }

    std::getline(in, line);
  }

  if(category=="") {
    USER_ERROR("category must be specified");
  }

  if(problemTimeLimit==-1) {
    USER_ERROR("problem time limit must be specified");
  }

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
    _problems.push(ProblemInfo(inp, outp));
  }

  while(!in.eof() && line=="") { std::getline(in, line); }
  if(line!="% SZS end BatchProblems") {
    USER_ERROR("\"% SZS end BatchProblems\" expected, \""+line+"\" found.");
  }
}

/**
 * Return intended slice time in milliseconds and assign the slice string with
 * chopped time to @b chopped.
 */
unsigned CMZRMode::getSliceTime(string sliceCode)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos=sliceCode.find_last_of('_');
  string sliceTimeStr=sliceCode.substr(pos+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense
  unsigned time = (unsigned)(sliceTime*100 * SLOWNESS) + 100;
  if (time < 1000) {
    time += 100;
  }
  return time;
}


///////////////////////
// strategy selector
//

/**
 * Add strategies for @c property to @c res so that the first strategy to try is
 * res[0].
 */
void CMZRMode::getStrategy(Property& property, StringStack& res)
{
  CALL("CMZRMode::getStrategy");

  unsigned atoms = property.atoms();
  unsigned prop = property.props();

  StringStack quick;
  StringStack fallback;

  fallback.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_600");
  fallback.push("ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_600");
  fallback.push("dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_600");
  fallback.push("dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600");
  fallback.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_300");
  fallback.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_300");
  fallback.push("dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_900");
  fallback.push("dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_300");
  fallback.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_300");
  fallback.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_300");
  fallback.push("dis+1002_8:1_bd=off:bs=unit_only:bsr=on:ep=on:flr=on:nwc=10:sswsr=on:sac=on:sgo=on:sio=off:sfv=off_300");
  fallback.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_600");
  fallback.push("dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_300");
  fallback.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_300");
  fallback.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_300");
  fallback.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_300");
  fallback.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_300");
  fallback.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_300");
  fallback.push("dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1200");
  fallback.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_300");
  fallback.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_1200");
  fallback.push("lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:ss=included:sio=off:spl=backtracking_600");
  fallback.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_300");
  fallback.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_600");
  fallback.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_300");
  fallback.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_300");
  fallback.push("ins+1010_4_bs=unit_only:flr=on:gsp=input_only:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.3:igwr=on:nwc=5:ptb=off:ssec=off:spl=off_300");
  fallback.push("dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_300");
  fallback.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_300");
  fallback.push("lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_300");
  fallback.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_300");
  fallback.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_600");
  fallback.push("dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_300");
  fallback.push("lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=backtracking_300");
  fallback.push("dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_300");
  fallback.push("dis-1010_5_bs=off:drc=off:ep=on:gsp=input_only:gs=on:nwc=2.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:swb=on:sp=reverse_arity_300");
  fallback.push("dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300");
  fallback.push("ott+2_3_bs=unit_only:bsr=unit_only:cond=fast:fde=none:gsp=input_only:nwc=1.2:ptb=off:ssec=off:sfv=off:sp=reverse_arity_300");
  fallback.push("ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_300");
  fallback.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_300");
  fallback.push("lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_300");
  fallback.push("lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_900");
  fallback.push("dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_600");

  if (atoms > 2000000) {
    // 1: CSR025+6 CSR026+6 CSR027+6 CSR028+6 CSR029+6 CSR030+6 CSR031+6 CSR032+6 CSR033+6 CSR034+6
    //   CSR036+6 CSR038+6 CSR039+6 CSR040+6 CSR041+6 CSR042+6 CSR043+6 CSR044+6 CSR045+6 CSR046+6
    //   CSR047+6 CSR048+6 CSR049+6 CSR050+6 CSR051+6 CSR052+6 CSR053+6 CSR054+6 CSR055+6 CSR056+6
    //   CSR057+6 CSR058+6 CSR060+6 CSR061+6 CSR062+6 CSR064+6 CSR065+6 CSR066+6 CSR067+6 CSR068+6
    //   CSR069+6 CSR070+6 CSR071+6 CSR072+6 CSR073+6 CSR074+6
    quick.push("dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_748");
    // 1: CSR035+6 CSR037+6 CSR059+6 CSR063+6
    // 2: CSR025+6 CSR031+6 CSR032+6 CSR042+6 CSR043+6 CSR047+6 CSR048+6 CSR051+6 CSR053+6 CSR057+6
    //   CSR064+6 CSR065+6 CSR067+6 CSR071+6 CSR073+6
    quick.push("dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_696");
  }
  else if (prop == 131087) {
    if (atoms > 300000) {
      // 1: ALG226+4 ALG227+4 ALG231+4 LAT345+4 LAT346+4 LAT347+4 LAT348+4 LAT356+4 LAT374+4 SEU406+4
      //   SEU408+4 SEU411+4 SEU424+4 SEU425+4 SEU427+4 SEU429+4 SEU430+4 SEU435+4 SEU444+4 SEU446+4
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_79");
      // 1: ALG232+4 LAT351+4 SEU418+4 SEU420+4 SEU449+4
      // 2: LAT347+4 LAT348+4 LAT356+4 SEU406+4 SEU411+4 SEU424+4 SEU429+4 SEU435+4 SEU444+4
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_49");
      // 1: CAT033+4 LAT361+4 LAT362+4 LAT376+4 SEU422+4 SEU451+4
      // 2: ALG226+4 ALG227+4 SEU427+4 SEU430+4
      // 3: SEU406+4 SEU411+4 SEU424+4 SEU429+4 SEU435+4 SEU444+4
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_98");
      // 1: TOP047+4
      // 2: LAT345+4
      // 3: ALG226+4 ALG227+4 LAT348+4 LAT356+4
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_44");
      // 1: LAT354+4 LAT355+4 LAT369+4 LAT370+4 SEU413+4
      // 2: LAT346+4 SEU422+4 SEU425+4
      // 3: LAT345+4 SEU427+4 SEU430+4
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_123");
      // 1: SEU417+4 SEU438+4
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_46");
      // 1: LAT338+4
      quick.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_31");
      // 1: LAT380+4
      // 2: LAT362+4
      // 3: LAT346+4
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_37");
      // 1: ALG223+4 ALG224+4
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_91");
      // 1: SEU432+4
      quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_46");
      // 1: LAT343+4 SEU407+4 SEU437+4
      // 2: CAT033+4 SEU413+4
      // 3: SEU422+4
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_213");
      // 1: SEU439+4
      // 3: SEU413+4
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82");
      // 1: SEU416+4
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_123");
    }
    else if (atoms>150000) {
      // 1: CAT025+4 GRP618+4 GRP641+4 GRP653+4 LAT300+4 LAT304+4 LAT305+4 LAT310+4 LAT319+4 LAT327+4
      //   LAT337+4 TOP028+4 TOP034+4
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_23");
      // 1: ALG214+4 ALG215+4 ALG216+4 ALG219+4 ALG220+4 CAT028+4 GRP628+4 GRP629+4 GRP631+4 GRP639+4
      //   GRP640+4 GRP642+4 GRP643+4 GRP644+4 GRP645+4 LAT286+4 LAT287+4 LAT288+4 LAT291+4 LAT292+4
      //   LAT295+4 LAT311+4 LAT312+4 LAT314+4 LAT331+4 LAT332+4 LAT333+4 TOP023+4 TOP024+4 TOP025+4
      //   TOP026+4 TOP027+4 TOP035+4
      // 2: GRP641+4 GRP653+4 LAT337+4 TOP028+4 TOP034+4
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_181");
      // 1: LAT297+4 LAT330+4
      // 2: ALG215+4 GRP618+4
      // 3: GRP641+4 TOP028+4
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_19");
      // 1: GRP632+4
      // 2: ALG216+4 GRP629+4 GRP631+4 GRP642+4 GRP643+4 GRP644+4 LAT305+4
      // 3: GRP618+4
      quick.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_20");
      // 1: GRP620+4 GRP648+4
      // 2: LAT297+4 LAT319+4 LAT327+4
      // 3: GRP643+4 GRP644+4 LAT305+4
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_20");
      // 1: TOP037+4
      // 2: LAT288+4 LAT295+4 LAT331+4
      // 3: GRP629+4 GRP642+4
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_23");
      // 1: LAT294+4 LAT296+4 LAT301+4 LAT302+4 LAT303+4 LAT306+4 LAT313+4 LAT322+4 LAT323+4
      // 2: ALG214+4 ALG219+4 ALG220+4 GRP628+4 LAT286+4 LAT287+4 LAT292+4 LAT300+4 LAT304+4 LAT332+4
      //   TOP023+4 TOP024+4 TOP025+4 TOP026+4 TOP027+4
      // 3: ALG215+4 ALG216+4 GRP653+4 LAT288+4 LAT295+4 LAT319+4 LAT327+4 LAT337+4 TOP034+4
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_161");
      // 1: CAT032+4
      // 2: CAT025+4
      quick.push("dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_15");
      // 1: ALG222+4 GRP637+4
      // 3: LAT286+4 LAT287+4 LAT292+4 LAT300+4 TOP024+4 TOP025+4
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_93");
      // 1: GRP652+4 LAT289+4
      // 2: GRP645+4 LAT313+4 TOP035+4
      // 3: ALG219+4 GRP628+4 GRP631+4 LAT331+4 LAT332+4
      quick.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_119");
      // 1: LAT290+4 TOP041+4 TOP042+4
      // 2: GRP639+4 LAT333+4
      // 3: ALG214+4 ALG220+4 GRP645+4 LAT297+4 TOP023+4 TOP035+4
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_194");
      // 1: CAT026+4 LAT298+4
      // 3: LAT304+4 LAT313+4
      quick.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_155");
      // 1: GRP634+4 LAT308+4
      // 2: LAT291+4 LAT301+4
      // 3: LAT333+4
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_169");
    }
    else if (atoms > 80000) {
      // 1: ALG226+3 ALG227+3 ALG231+3 GRP641+3 GRP642+3 LAT295+3 LAT297+3 LAT300+3 LAT337+3 LAT345+3
      //   LAT346+3 LAT348+3 LAT356+3 LAT374+3 SEU406+3 SEU411+3 SEU413+3 SEU424+3 SEU425+3 SEU427+3
      //   SEU429+3 SEU430+3 SEU435+3 SEU444+3 TOP023+3 TOP024+3 TOP025+3 TOP034+3 TOP041+3 TOP042+3
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_19");
      // 1: LAT331+3 TOP026+3 TOP027+3 TOP037+3
      // 2: ALG226+3 GRP641+3 GRP642+3 LAT295+3 SEU424+3 SEU429+3
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8");
      // 1: CAT033+3 GRP637+3 GRP643+3 GRP644+3 LAT305+3 SEU422+3 SEU449+3 TOP028+3
      // 2: ALG227+3 LAT300+3 LAT348+3 SEU406+3 SEU427+3 SEU430+3 SEU435+3 SEU444+3 TOP024+3 TOP025+3
      //   TOP034+3
      // 3: ALG226+3 GRP641+3 GRP642+3 LAT295+3 SEU424+3 SEU429+3
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_43");
      // 1: GRP648+3 LAT319+3 LAT327+3
      // 2: GRP643+3 GRP644+3 LAT297+3 LAT305+3
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7");
      // 1: LAT301+3 LAT304+3 LAT308+3 LAT313+3 LAT332+3 SEU446+3
      // 2: CAT033+3 LAT319+3 LAT331+3 LAT337+3 LAT346+3 SEU425+3
      // 3: ALG227+3 LAT300+3 LAT348+3 SEU430+3 SEU435+3 SEU444+3 TOP024+3 TOP025+3 TOP034+3
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_26");
      // 1: LAT330+3
      // 2: LAT304+3
      // 3: LAT297+3
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_7");
      // 1: LAT362+3 LAT376+3 SEU445+3 TOP035+3
      // 2: LAT345+3 LAT356+3 SEU446+3 TOP026+3 TOP027+3
      // 3: GRP643+3 GRP644+3 LAT331+3 LAT346+3
      quick.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_10");
      // 1: LAT298+3 SEU451+3
      // 2: SEU411+3 TOP035+3
      // 3: SEU406+3 SEU427+3 TOP026+3 TOP027+3
      quick.push("dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_27");
      // 1: SEU439+3
      // 3: SEU411+3
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_16");
      // 1: LAT333+3 TOP047+3
      // 2: LAT301+3 LAT332+3 LAT374+3 SEU413+3
      // 3: LAT337+3 LAT345+3 LAT356+3
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_19");
      // 1: GRP640+3 GRP645+3 GRP653+3 LAT311+3 LAT312+3 LAT347+3 LAT355+3
      // 2: LAT333+3 TOP023+3 TOP028+3
      // 3: CAT033+3 LAT332+3 SEU425+3 SEU446+3 TOP035+3
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_77");
      // 1: LAT363+3
      // 2: LAT376+3
      // 3: SEU413+3
      quick.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_21");
      // 1: LAT310+3 LAT380+3
      // 2: GRP653+3 LAT327+3 LAT362+3
      // 3: LAT304+3 LAT305+3 LAT319+3 TOP028+3
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_12");
      // 1: LAT323+3 LAT338+3 LAT361+3 LAT377+3
      // 2: LAT313+3 SEU422+3 SEU451+3
      // 3: LAT301+3 LAT327+3 LAT362+3 LAT376+3
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_86");
      // 1: SEU417+3 SEU418+3 SEU438+3
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_14");
      // 1: ALG232+3 LAT351+3 SEU420+3
      // 2: SEU449+3
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_14");
      // 1: ALG223+3 ALG224+3
      // 2: LAT310+3
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_66");
      // 1: LAT294+3 LAT296+3 LAT302+3 LAT303+3 LAT306+3 LAT322+3 LAT354+3 LAT369+3 LAT370+3 SEU408+3
      // 2: GRP640+3 LAT323+3 LAT355+3
      // 3: GRP653+3 LAT313+3 SEU422+3 TOP023+3
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_144");
      // 1: SEU416+3
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_71");
      // 1: LAT314+3
      // 2: GRP645+3 LAT354+3
      // 3: LAT333+3 LAT355+3 LAT374+3
      quick.push("lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_91");
      // 1: LAT343+3 SEU437+3 SEU441+3
      // 2: SEU417+3
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_290");
      // 1: SEU440+3
      // 2: SEU441+3
      quick.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_150");
      // 1: SEU407+3
      // 3: SEU451+3
      quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_172");
      // 1: GRP638+3 GRP639+3
      // 2: LAT302+3
      // 3: GRP645+3 LAT323+3
      quick.push("lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_182");
    }
    else {
      // 1: ALG219+2 ALG227+2 GRP618+2 GRP629+2 GRP641+2 GRP642+2 GRP643+2 GRP644+2 SEU406+2 SEU417+2
      //   SEU422+2 SEU427+2 SEU430+2 SEU438+2 SEU444+2 SEU451+2 TOP026+2 TOP027+2 TOP035+2
      quick.push("dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_2");
      // 1: ALG214+2 ALG214+3 ALG215+2 ALG215+3 ALG216+2 ALG216+3 ALG219+3 ALG220+2 ALG220+3 ALG226+2
      //   GRP628+2 GRP628+3 GRP629+3 GRP653+2 LAT286+2 LAT286+3 LAT287+2 LAT287+3 LAT288+2 LAT288+3
      //   LAT292+2 LAT292+3 LAT294+2 LAT296+2 LAT300+2 LAT301+2 LAT302+2 LAT303+2 LAT304+2 LAT313+2
      //   LAT319+2 LAT323+2 LAT345+2 LAT346+2 LAT369+2 SEU408+2 SEU413+2 TOP024+2 TOP025+2
      // 2: ALG219+2 ALG227+2 GRP629+2 GRP641+2 GRP642+2 GRP644+2 SEU406+2 SEU422+2 SEU427+2 SEU430+2
      //   SEU444+2 TOP026+2 TOP027+2
      quick.push("dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_16");
      // 1: CAT025+2 CAT032+2
      // 3: SEU444+2
      quick.push("dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_4");
      // 1: CAT031+2 CAT031+3 CAT033+2 LAT327+2 LAT362+2 SEU446+2
      // 2: ALG215+2 ALG226+2 LAT286+2 LAT287+2 LAT287+3 LAT292+2 LAT292+3 LAT300+2 LAT304+2 LAT319+2
      //   LAT346+2 SEU451+2
      // 3: ALG227+2 GRP642+2 SEU406+2
      quick.push("lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_17");
      // 1: GRP618+3 GRP631+2 GRP631+3 LAT297+2 LAT322+2 LAT332+2 LAT333+2 LAT343+2 LAT376+2 SEU411+2
      //   SEU437+2 SEU441+2 TOP034+2
      // 2: ALG214+2 ALG214+3 ALG215+3 ALG216+2 ALG220+2 ALG220+3 CAT033+2 GRP618+2 GRP628+2 GRP629+3
      //   GRP643+2 LAT286+3 LAT288+2 LAT288+3 LAT345+2 SEU413+2 SEU417+2 TOP024+2
      // 3: ALG215+2 ALG226+2 GRP629+2 GRP641+2 GRP644+2 LAT286+2 LAT287+2 LAT287+3 LAT300+2 LAT304+2
      //   SEU422+2 SEU427+2 SEU430+2 SEU451+2
      quick.push("ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_48");
      // 1: CAT030+2 CAT034+2 GRP645+2 LAT289+2 LAT291+2 LAT291+3 LAT331+2 LAT337+2 LAT355+2 LAT356+2
      //   LAT374+2 TOP047+2
      // 2: ALG219+3 LAT313+2 LAT332+2 LAT333+2 TOP034+2
      // 3: ALG219+2 GRP628+2 GRP629+3 LAT292+2 LAT292+3 LAT345+2 LAT346+2 SEU413+2
      quick.push("ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_61");
      // 1: ALG224+2 TOP037+2
      // 2: GRP618+3 LAT331+2
      // 3: GRP618+2 LAT288+2 LAT288+3 TOP026+2 TOP027+2
      quick.push("lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8");
      // 1: ALG223+2 LAT310+2 TOP028+2
      // 2: ALG224+2 LAT297+2 SEU411+2
      // 3: ALG215+3 GRP643+2 TOP034+2
      quick.push("dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_36");
      // 1: ALG225+1 GRP639+2 LAT295+2 LAT305+2 LAT309+2
      // 2: GRP631+2 GRP645+2 LAT289+2 LAT291+2 LAT291+3 LAT310+2 LAT374+2 TOP028+2
      // 3: ALG214+2 ALG219+3 LAT286+3 LAT313+2 LAT332+2 TOP024+2
      quick.push("dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_70");
      // 1: GRP637+2 SEU424+2 SEU449+2
      // 2: LAT305+2 TOP025+2
      // 3: ALG216+2 CAT033+2 GRP618+3 TOP028+2
      quick.push("dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_23");
      // 1: SEU445+2
      // 2: SEU446+2
      // 3: LAT331+2
      quick.push("lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_3");
      // 1: ALG231+2
      // 2: GRP631+3 LAT356+2
      // 3: GRP631+2 GRP645+2 LAT291+2 LAT291+3 LAT297+2 SEU417+2
      quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_29");
      // 1: SEU439+2
      quick.push("dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9");
      // 1: SEU407+2 SEU418+2
      // 2: ALG216+3 LAT327+2 TOP035+2
      // 3: LAT305+2 LAT319+2 TOP025+2
      quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_9");
      // 1: GRP620+3 GRP648+2
      // 3: LAT327+2
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7");
      // 1: LAT380+2
      // 2: GRP653+2 LAT337+2 LAT362+2
      // 3: LAT310+2
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_7");
      // 1: LAT351+2 SEU420+2
      // 2: SEU449+2
      // 3: LAT356+2
      quick.push("ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_7");
      // 1: CAT028+2 CAT028+3 GRP640+2 LAT290+3 LAT299+2 LAT311+2 LAT312+2 LAT347+2 LAT354+2 SEU425+2
      //   TOP023+2
      // 2: GRP628+3 LAT295+2 LAT355+2 SEU441+2
      // 3: ALG214+3 ALG216+3 ALG220+2 ALG220+3 GRP631+3 GRP653+2 SEU411+2 SEU446+2 TOP035+2
      quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_86");
      // 1: LAT338+2
      quick.push("ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_7");
      // 1: LAT330+2
      quick.push("dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_4");
      // 1: GRP620+2 GRP634+2 GRP634+3 LAT306+2 LAT308+2 LAT348+2 LAT370+2
      // 2: LAT301+2 LAT369+2 SEU408+2 SEU425+2
      // 3: LAT295+2 LAT333+2 LAT337+2
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_91");
      // 1: ALG222+2 ALG222+3 LAT363+2 SEU429+2 SEU435+2 TOP041+2 TOP042+2
      // 2: GRP640+2 LAT299+2 LAT347+2 LAT376+2
      // 3: GRP628+3
      quick.push("dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_94");
      // 1: GRP624+2 LAT289+3 LAT361+2 LAT377+2
      // 2: LAT323+2
      // 3: LAT301+2 LAT362+2 LAT376+2
      quick.push("dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_89");
      // 1: ALG218+2 ALG218+3 GRP632+2 GRP632+3
      quick.push("lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_134");
      // 1: SEU440+2
      // 3: SEU441+2
      quick.push("ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_76");
      // 1: SEU416+2
      quick.push("ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_73");
      // 1: CAT026+3
      // 2: ALG225+1 LAT294+2
      // 3: LAT289+2
      quick.push("ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_95");
      // 1: LAT298+2 LAT379+2
      // 2: GRP632+3 SEU418+2 SEU420+2
      quick.push("lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_277");
      // 1: CAT025+3 CAT032+3
      quick.push("dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6");
      // 1: LAT290+2 LAT326+2
      // 2: LAT354+2 TOP023+2 TOP041+2 TOP042+2
      // 3: LAT294+2 LAT347+2 LAT355+2 LAT374+2 SEU408+2 SEU425+2
      quick.push("dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_135");
    }
  }
  else  {
      // 1: CSR025+3 CSR026+2 CSR026+3 CSR027+2 CSR028+3 CSR029+3 CSR030+3 CSR031+3 CSR032+3 CSR033+3
      //   CSR034+2 CSR034+3 CSR035+3 CSR037+3 CSR041+3 CSR042+3 CSR043+3 CSR044+2 CSR045+3 CSR046+3
      //   CSR047+3 CSR048+3 CSR050+2 CSR050+3 CSR051+3 CSR053+3 CSR054+3 CSR055+3 CSR056+3 CSR057+2
      //   CSR057+3 CSR058+3 CSR059+3 CSR060+2 CSR061+2 CSR062+2 CSR062+3 CSR063+3 CSR064+2 CSR064+3
      //   CSR065+2 CSR065+3 CSR067+3 CSR068+3 CSR069+3 CSR070+2 CSR070+3 CSR071+2 CSR071+3 CSR072+3
      //   CSR073+2 CSR073+3 CSR074+3
      quick.push("dis+1011_3_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity_3");
      // 1: ALG216+1 ALG218+1 ALG219+1 ALG220+1 ALG222+1 CAT025+1 CAT026+1 CAT032+1 CAT033+1 CSR075+1
      //   CSR079+4 CSR082+4 CSR083+1 CSR085+1 CSR085+4 CSR085+5 CSR086+1 CSR086+4 CSR086+5 CSR089+4
      //   CSR089+5 CSR090+4 CSR090+5 CSR092+1 CSR094+1 CSR094+4 CSR096+4 CSR098+1 CSR098+4 CSR098+5
      //   CSR099+1 CSR099+4 CSR100+1 CSR100+4 CSR100+5 CSR101+1 CSR101+4 CSR101+5 CSR103+1 CSR103+4
      //   CSR103+5 CSR108+1 CSR108+4 CSR109+1 CSR118+1 GRP618+1 GRP619+1 GRP620+1 GRP622+1 GRP624+1
      //   GRP628+1 GRP632+1 GRP637+1 GRP638+1 GRP639+1 GRP640+1 GRP641+1 GRP642+1 GRP645+1 GRP653+1
      //   LAT291+1 LAT292+1 LAT294+1 LAT297+1 LAT301+1 LAT302+1 LAT303+1 LAT304+1 LAT305+1 LAT310+1
      //   LAT313+1 LAT319+1 LAT323+1 LAT326+1 LAT337+1 LAT346+1 LAT356+1 LAT359+1 LAT362+1 LAT376+1
      //   LAT379+1 SEU406+1 SEU407+1 SEU408+1 SEU412+1 SEU413+1 SEU417+1 SEU425+1 SEU449+1 SEU451+1
      //   TOP025+1 TOP035+1
      quick.push("dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_2");
      // 1: CSR038+2 CSR039+2 CSR040+3 CSR044+3 CSR049+2 CSR052+3 CSR063+2
      // 2: CSR025+3 CSR026+2 CSR026+3 CSR028+3 CSR029+3 CSR030+3 CSR031+3 CSR032+3 CSR034+2 CSR034+3
      //   CSR035+3 CSR037+3 CSR041+3 CSR042+3 CSR043+3 CSR044+2 CSR045+3 CSR046+3 CSR047+3 CSR048+3
      //   CSR050+2 CSR050+3 CSR051+3 CSR053+3 CSR054+3 CSR055+3 CSR056+3 CSR057+2 CSR057+3 CSR058+3
      //   CSR059+3 CSR060+2 CSR061+2 CSR062+2 CSR062+3 CSR063+3 CSR064+2 CSR064+3 CSR065+2 CSR065+3
      //   CSR067+3 CSR068+3 CSR069+3 CSR071+2 CSR071+3 CSR072+3 CSR073+2 CSR073+3 CSR074+3
      quick.push("tab+10_1_gsp=input_only:spl=off:tbsr=off:tfsr=off:tgawr=1/128:tglr=1/7:tipr=off:tlawr=1/2_2");
      // 1: CSR036+3 CSR039+3 CSR049+3 CSR061+3
      // 2: CSR033+3 CSR052+3
      // 3: CSR025+3 CSR028+3 CSR029+3 CSR032+3 CSR034+2 CSR034+3 CSR035+3 CSR037+3 CSR041+3 CSR042+3
      //   CSR043+3 CSR046+3 CSR047+3 CSR048+3 CSR050+2 CSR050+3 CSR051+3 CSR053+3 CSR054+3 CSR058+3
      //   CSR059+3 CSR062+2 CSR067+3 CSR069+3 CSR072+3 CSR074+3
      quick.push("dis+1004_7_bs=off:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sos=on:sagn=off:spo=on:spl=backtracking:updr=off_2");
      // 1: ALG214+1 LAT352+1 LAT353+1 LAT367+1 LAT369+1 LAT378+1 SEU411+1
      // 2: ALG219+1 ALG220+1 CAT033+1 CSR083+1 CSR085+1 CSR085+4 CSR098+1 CSR098+4 CSR103+1 CSR103+4
      //   GRP618+1 GRP640+1 GRP653+1 LAT291+1 LAT292+1 LAT294+1 LAT297+1 LAT313+1 LAT319+1 LAT323+1
      //   LAT326+1 LAT362+1 LAT379+1 SEU408+1 SEU413+1 TOP025+1 TOP035+1
      quick.push("dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_1");
      // 1: LAT288+1 LAT289+1 LAT363+1 SEU418+1 SEU439+1 SEU448+1 TOP023+1
      // 2: ALG214+1 CSR085+5 CSR098+5 CSR103+5 GRP628+1 GRP637+1 GRP638+1 GRP639+1 GRP645+1 LAT352+1
      //   LAT353+1 LAT369+1 SEU411+1 SEU417+1 SEU449+1
      // 3: ALG220+1 CAT033+1 CSR083+1 CSR085+1 CSR085+4 CSR098+1 CSR098+4 CSR103+1 CSR103+4 GRP618+1
      //   GRP640+1 LAT291+1 LAT292+1 LAT294+1 LAT319+1 LAT379+1 SEU413+1 TOP025+1 TOP035+1
      quick.push("dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_2");
      // 1: ALG226+1 GRP621+1 LAT311+1 LAT322+1 LAT347+1 LAT366+1 LAT370+1 TOP024+1
      // 2: ALG216+1 GRP620+1 LAT363+1 LAT376+1 TOP023+1
      // 3: ALG219+1 CSR098+5 CSR103+5 GRP628+1 LAT326+1 LAT352+1 LAT353+1 LAT369+1 SEU411+1 SEU417+1
      //   SEU449+1
      quick.push("dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_3");
      // 1: ALG224+1 CSR025+4 CSR026+4 CSR028+4 CSR029+4 CSR030+4 CSR031+4 CSR033+4 CSR034+4 CSR035+4
      //   CSR037+4 CSR042+4 CSR043+4 CSR046+4 CSR047+4 CSR048+4 CSR050+4 CSR051+4 CSR053+4 CSR054+4
      //   CSR055+4 CSR056+4 CSR057+4 CSR058+4 CSR059+4 CSR062+4 CSR063+4 CSR064+4 CSR065+4 CSR067+4
      //   CSR069+4 CSR070+4 CSR071+4 CSR072+4 CSR073+4 CSR074+4 CSR083+2 CSR098+2 CSR103+2 GRP647+1
      //   LAT283+1 LAT284+1 LAT286+1 LAT287+1 LAT296+1 LAT306+1 LAT307+1 LAT308+1 LAT309+1 LAT312+1
      //   LAT324+1 LAT328+1 LAT331+1 LAT332+1 LAT338+1 LAT343+1 LAT345+1 SEU427+1 SEU440+1 SEU441+1
      //   SEU450+1 TOP036+1 TOP037+1 TOP042+1 TOP047+1
      // 2: CAT025+1 CAT032+1 GRP624+1 GRP641+1 GRP642+1 LAT289+1 LAT301+1 LAT302+1 LAT303+1 LAT304+1
      //   LAT305+1 LAT310+1 LAT311+1 LAT322+1 LAT337+1 LAT346+1 LAT347+1 LAT356+1 LAT370+1 SEU425+1
      //   SEU448+1 TOP024+1
      // 3: ALG214+1 ALG216+1 GRP620+1 GRP637+1 GRP638+1 GRP639+1 GRP645+1 GRP653+1 LAT313+1 LAT323+1
      //   LAT363+1 SEU408+1 TOP023+1
      quick.push("ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_20");
      // 1: ALG223+1 CSR032+4 CSR036+4 CSR039+4 CSR041+4 CSR049+4 CSR052+4 CSR061+4 CSR068+4 CSR076+4
      //   CSR079+1 CSR079+5 CSR082+1 CSR083+4 CSR086+6 CSR090+1 CSR096+1 CSR096+5 CSR100+6 CSR101+6
      //   CSR104+1 CSR104+5 CSR108+2 GRP623+1 LAT295+1 LAT317+1 LAT321+1 LAT340+1 LAT354+1 LAT377+1
      //   SEU422+1 TOP029+1
      // 2: ALG224+1 CAT026+1 CSR025+4 CSR026+4 CSR028+4 CSR029+4 CSR030+4 CSR033+4 CSR034+4 CSR035+4
      //   CSR037+4 CSR042+4 CSR043+4 CSR046+4 CSR047+4 CSR048+4 CSR050+4 CSR051+4 CSR053+4 CSR054+4
      //   CSR056+4 CSR057+4 CSR058+4 CSR059+4 CSR062+4 CSR065+4 CSR067+4 CSR069+4 CSR071+4 CSR072+4
      //   CSR073+4 CSR074+4 CSR075+1 CSR086+1 CSR090+5 CSR094+1 CSR100+1 CSR100+5 CSR101+1 CSR101+5
      //   CSR108+1 CSR118+1 LAT283+1 LAT284+1 LAT286+1 LAT287+1 LAT288+1 LAT296+1 LAT306+1 LAT307+1
      //   LAT309+1 LAT331+1 LAT332+1 LAT338+1 LAT343+1 LAT378+1 SEU406+1 TOP037+1
      // 3: GRP624+1 GRP641+1 GRP642+1 LAT289+1 LAT297+1 LAT301+1 LAT302+1 LAT303+1 LAT304+1 LAT305+1
      //   LAT310+1 LAT311+1 LAT322+1 LAT337+1 LAT346+1 LAT347+1 LAT356+1 LAT362+1 LAT376+1 TOP024+1
      quick.push("dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_60");
      // 1: ALG215+1 LAT329+1 LAT350+1 LAT351+1 SEU437+1
      // 2: ALG218+1 CSR079+4 CSR079+5 CSR083+2 CSR089+4 CSR098+2 CSR099+1 CSR100+4 CSR103+2 CSR109+1
      //   GRP619+1 GRP622+1 GRP623+1 LAT324+1 LAT359+1 SEU407+1 SEU422+1 SEU451+1 TOP047+1
      // 3: CAT025+1 CAT026+1 CAT032+1 CSR025+4 CSR028+4 CSR043+4 CSR046+4 CSR072+4 CSR075+1 CSR085+5
      //   CSR086+1 CSR094+1 CSR100+1 CSR100+5 CSR108+1 CSR118+1 LAT288+1 LAT331+1 LAT332+1 LAT378+1
      //   SEU406+1 SEU425+1
      quick.push("dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_8");
      // 1: LAT314+1
      // 2: CSR032+4 CSR041+4 CSR052+4 CSR061+4 CSR068+4 LAT377+1
      // 3: CSR029+4 CSR030+4 CSR033+4 CSR034+4 CSR035+4 CSR037+4 CSR042+4 CSR048+4 CSR050+4 CSR051+4
      //   CSR053+4 CSR054+4 CSR056+4 CSR057+4 CSR058+4 CSR062+4 CSR065+4 CSR067+4 CSR071+4 CSR073+4
      //   CSR074+4 GRP623+1 LAT286+1 LAT287+1 LAT296+1 LAT307+1 LAT324+1 LAT338+1 LAT343+1 SEU422+1
      //   TOP037+1
      quick.push("dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_15");
      // 1: CSR075+4 CSR076+1 CSR081+1 CSR081+4 CSR083+3 CSR084+1 CSR084+4 CSR085+2 CSR085+6 CSR091+4
      //   CSR092+5 CSR093+2 CSR093+4 CSR094+6 CSR098+6 CSR099+2 CSR099+5 CSR099+6 CSR101+2 CSR103+3
      //   CSR103+6 CSR104+4 CSR108+5 CSR109+4 CSR118+4 SEU410+1
      // 2: CSR031+4 CSR055+4 CSR063+4 CSR064+4 CSR070+4 CSR079+1 CSR082+1 CSR082+4 CSR083+4 CSR086+4
      //   CSR090+4 CSR092+1 CSR094+4 CSR096+1 CSR096+4 CSR096+5 CSR099+4 CSR108+2 CSR108+4 LAT312+1
      //   LAT350+1 LAT351+1 SEU427+1
      // 3: ALG218+1 CSR026+4 CSR032+4 CSR047+4 CSR059+4 CSR068+4 CSR069+4 CSR079+4 CSR079+5 CSR083+2
      //   CSR089+4 CSR090+5 CSR098+2 CSR099+1 CSR100+4 CSR101+1 CSR103+2 CSR109+1 SEU407+1
      quick.push("ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_101");
      // 1: CSR027+3 CSR038+3 CSR060+3 CSR066+2 CSR066+3
      // 2: CSR027+2 CSR038+2 CSR070+2
      // 3: CSR026+2 CSR026+3 CSR030+3 CSR031+3 CSR033+3 CSR044+2 CSR055+3 CSR056+3 CSR057+2 CSR057+3
      //   CSR060+2 CSR061+2 CSR062+3 CSR063+3 CSR064+2 CSR064+3 CSR065+2 CSR065+3 CSR068+3 CSR071+2
      //   CSR071+3 CSR073+2 CSR073+3
      quick.push("dis-1002_5:1_bs=unit_only:bsr=unit_only:flr=on:gsp=input_only:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sswn=on:sos=on:spo=on:swb=on:sp=occurrence_3");
      // 1: CSR027+4 CSR038+4 CSR044+4 CSR066+4 CSR075+2 CSR075+3 CSR081+2 CSR081+3 CSR082+2 CSR082+3
      //   CSR082+6 CSR084+2 CSR085+3 CSR086+2 CSR086+3 CSR088+3 CSR090+2 CSR090+3 CSR090+6 CSR092+2
      //   CSR092+3 CSR094+2 CSR096+2 CSR096+3 CSR099+3 CSR104+2 CSR104+3 CSR104+6 CSR105+3 CSR107+3
      //   CSR109+2 CSR109+3 CSR109+5 CSR118+2
      // 2: ALG215+1 CSR081+1 CSR083+3 CSR085+2 CSR085+6 CSR086+5 CSR086+6 CSR090+1 CSR099+2 CSR099+5
      //   CSR099+6 CSR103+3 CSR103+6 CSR104+1 CSR104+4 CSR104+5
      // 3: CSR031+4 CSR041+4 CSR055+4 CSR063+4 CSR082+1 CSR086+4 CSR090+4 CSR092+1 CSR096+1 CSR099+4
      quick.push("dis+10_64_bs=off:bms=on:cond=on:drc=off:gsp=input_only:nwc=1.1:ssec=off:sd=3:ss=axioms:sgo=on:sio=off:spo=on:sp=occurrence_40");
      // 1: CAT028+1 LAT380+1 SEU420+1 TOP038+1 TOP039+1 TOP040+1 TOP041+1
      // 2: ALG222+1 ALG223+1 CSR075+4 CSR098+6 CSR101+4 GRP632+1 LAT317+1 LAT345+1 SEU439+1 SEU441+1
      //   TOP042+1
      // 3: ALG215+1 ALG224+1 CSR085+2 GRP619+1 GRP622+1 LAT370+1 LAT377+1 SEU451+1 TOP047+1
      quick.push("ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_35");
      // 1: CSR098+3 GRP648+1 GRP652+1 TOP032+1 TOP033+1
      // 2: CAT028+1 GRP621+1 GRP647+1 LAT328+1 SEU450+1 TOP036+1
      // 3: ALG223+1 CSR083+3 CSR098+6 CSR103+3 CSR103+6 LAT283+1 LAT284+1 LAT306+1 LAT309+1 LAT312+1
      //   LAT359+1 SEU427+1 SEU441+1 SEU448+1 TOP042+1
      quick.push("ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_46");
      // 1: LAT330+1 LAT374+1
      // 2: LAT380+1
      // 3: CSR101+4 LAT351+1
      quick.push("lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_1");
      // 1: GRP630+1
      // 3: LAT328+1
      quick.push("dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_9");
      // 1: CSR060+4 CSR079+2 CSR079+3 CSR093+1 CSR093+3 CSR094+3 CSR096+6 CSR118+3
      // 2: CSR027+4 CSR038+4 CSR044+4 CSR066+4 CSR075+2 CSR075+3 CSR081+2 CSR081+3 CSR082+2 CSR082+3
      //   CSR082+6 CSR084+2 CSR085+3 CSR086+2 CSR090+2 CSR090+3 CSR090+6 CSR092+2 CSR093+2 CSR094+2
      //   CSR096+2 CSR099+3 CSR104+2 CSR104+3 CSR104+6 CSR109+2 CSR109+3 CSR109+5 CSR118+2
      // 3: CSR052+4 CSR061+4 CSR079+1 CSR081+1 CSR085+6 CSR086+5 CSR086+6 CSR090+1 CSR099+2 CSR099+5
      //   CSR099+6 CSR104+1 CSR104+4 CSR104+5
      quick.push("tab+10_1_ep=RST:ss=axioms:spl=off:tbsr=off:tgawr=1/16:tglr=4/1:tipr=off:tlawr=1/50_43");
      // 1: CSR040+4 CSR076+2 CSR083+5 CSR089+1 CSR091+1 CSR100+2 CSR118+5 LAT339+1 SEU445+1 SEU446+1
      //   SEU447+1
      // 2: CSR049+4 CSR079+2 CSR101+2 CSR108+5 CSR109+4 CSR118+4
      // 3: ALG222+1 CSR027+4 CSR038+4 CSR064+4 CSR066+4 CSR075+2 CSR075+4 CSR082+2 CSR082+4 CSR083+4
      //   CSR086+2 CSR094+2 CSR094+4 CSR096+4 CSR096+5 CSR101+5 CSR108+2 CSR108+4 CSR109+2 CSR118+2
      //   LAT350+1
      quick.push("ott+1011_3:1_bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_45");
      // 1: CAT029+1 CAT031+1 CAT034+1 CSR025+5 CSR028+5 CSR035+5 CSR043+5 CSR045+4 CSR046+5 CSR051+5
      //   CSR053+5 CSR054+5 CSR058+5 CSR069+5 CSR072+5 CSR075+5 CSR075+6 CSR076+6 CSR079+6 CSR080+6
      //   CSR081+6 CSR082+5 CSR083+6 CSR084+5 CSR084+6 CSR088+6 CSR089+2 CSR089+6 CSR091+2 CSR091+5
      //   CSR092+4 CSR092+6 CSR093+6 CSR094+5 CSR108+6 CSR109+6 CSR118+6 LAT357+1 LAT358+1 LAT361+1
      // 2: CSR060+4 CSR076+1 CSR083+5 CSR084+1 CSR084+4 CSR089+1 CSR089+5 CSR091+1 CSR091+4 CSR092+5
      //   CSR094+3 CSR094+6 CSR096+6 CSR098+3 CSR100+2 CSR100+6 CSR101+6 CSR118+3 CSR118+5 SEU447+1
      // 3: CSR044+4 CSR070+4 CSR075+3 CSR079+2 CSR082+3 CSR082+6 CSR085+3 CSR090+6 CSR092+2 CSR096+2
      //   CSR099+3 CSR101+2 CSR104+6 CSR108+5 CSR109+4 CSR109+5 CSR118+4 LAT380+1
      quick.push("ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_288");
      // 1: CSR084+3 CSR089+3 CSR100+3 CSR101+3 CSR108+3
      // 2: CSR079+3 CSR086+3 CSR092+3 CSR096+3
      // 3: CSR081+2 CSR081+3 CSR084+1 CSR084+2 CSR096+6 CSR098+3 CSR100+2 CSR100+6 CSR101+6 CSR109+3
      //   GRP632+1 LAT345+1
      quick.push("lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_43");
      // 1: CAT027+1 CSR026+5 CSR027+5 CSR029+5 CSR030+5 CSR031+5 CSR032+5 CSR033+5 CSR034+5 CSR036+5
      //   CSR037+5 CSR038+5 CSR039+5 CSR040+5 CSR041+5 CSR042+5 CSR044+5 CSR045+5 CSR047+5 CSR048+5
      //   CSR049+5 CSR050+5 CSR052+5 CSR055+5 CSR056+5 CSR057+5 CSR059+5 CSR060+5 CSR061+5 CSR062+5
      //   CSR063+5 CSR064+5 CSR065+5 CSR066+5 CSR067+5 CSR068+5 CSR070+5 CSR071+5 CSR073+5 CSR074+5
      // 2: CAT031+1 CSR025+5 CSR028+5 CSR035+5 CSR040+4 CSR043+5 CSR045+4 CSR046+5 CSR051+5 CSR053+5
      //   CSR054+5 CSR058+5 CSR069+5 CSR072+5 CSR075+5 CSR089+2 CSR091+5 CSR092+4 CSR094+5 GRP648+1
      //   LAT295+1 LAT374+1
      // 3: CSR076+1 CSR083+5 CSR084+4 CSR089+1 CSR089+5 CSR091+1 CSR091+4 GRP621+1
      quick.push("dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_200");
      // 1: CSR076+3 CSR081+5 CSR091+3 CSR091+6
      // 2: CAT034+1 CSR036+4 CSR039+4 CSR075+6 CSR076+4 CSR079+6 CSR081+4 CSR081+6 CSR082+5 CSR083+6
      //   CSR091+2 CSR092+6 CSR100+3 CSR101+3 CSR118+6 TOP041+1
      // 3: CSR045+4 CSR049+4 CSR075+5 CSR079+3 CSR086+3 CSR090+2 CSR090+3 CSR091+5 CSR092+3 CSR092+4
      //   CSR092+5 CSR094+3 CSR094+5 CSR094+6 CSR096+3 CSR104+2 CSR104+3 CSR118+3 CSR118+5
      quick.push("dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_197");
      // 1: GRP646+1 TOP048+1
      // 2: TOP029+1
      // 3: CAT028+1 CSR101+3 GRP647+1 SEU450+1 TOP036+1 TOP041+1
      quick.push("lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:stl=30:sos=on:sac=on:sio=off:spo=on:spl=backtracking_153");
      // 1: CSR076+5
      // 3: CSR025+5 CSR028+5 CSR035+5 CSR040+4 CSR043+5 CSR046+5 CSR051+5 CSR053+5 CSR058+5 CSR069+5
      //   CSR072+5 CSR076+4 CSR082+5 GRP648+1 LAT295+1 LAT374+1
      quick.push("ott+2_3_bs=unit_only:bsr=unit_only:cond=fast:fde=none:gsp=input_only:nwc=1.2:ptb=off:ssec=off:sfv=off:sp=reverse_arity_206");
      // 1: GRP631+1 LAT298+1 LAT299+1 LAT355+1 TOP046+1
      // 2: CAT029+1 CSR093+4 LAT354+1 LAT361+1 SEU446+1
      // 3: CAT031+1 CAT034+1 SEU447+1
      quick.push("ins+1010_4_bs=unit_only:flr=on:gsp=input_only:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.3:igwr=on:nwc=5:ptb=off:ssec=off:spl=off_274");
      // 1: CSR036+2
      // 2: CSR039+2 CSR049+2 CSR061+3
      quick.push("dis+1011_2_bs=off:flr=on:gsp=input_only:gs=on:lcm=predicate:nwc=1:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:updr=off_1");
  }

  res = fallback;
  res.loadFromIterator(StringStack::BottomFirstIterator(quick));
}


#endif //!COMPILER_MSVC
