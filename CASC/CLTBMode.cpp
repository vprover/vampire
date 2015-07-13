/**
 * @file CLTBMode.cpp
 * Implements class CLTBMode.
 * @since 03/06/2013 updated to conform to the CASC-J6 specification
 * @author Andrei Voronkov
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
#include "Lib/ScopedPtr.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "CASCMode.hpp"

#include "CLTBMode.hpp"

#define SLOWNESS 1.15

using namespace CASC;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 * @since 05/06/2013 Vienna, adapted for CASC-J6
 * @author Andrei Voronkov
 */
void CLTBMode::perform()
{
  CALL("CLTBMode::perform");

  if (env.options->inputFile() == "") {
    USER_ERROR("Input file must be specified for cltb mode");
  }
  // to prevent from terminating by time limit
  env.options->setTimeLimitInSeconds(100000);

  UIHelper::cascMode = true;
  env.options->setProof(Options::Proof::TPTP);
  env.options->setStatistics(Options::Statistics::NONE);

  vstring line;
  ifstream in(env.options->inputFile().c_str());
  if (in.fail()) {
    USER_ERROR("Cannot open input file: " + env.options->inputFile());
  }

  //support several batches in one file
  while (!in.eof()) {
    vostringstream singleInst;
    bool ready = false;
    while (!in.eof()) {
      getline(in, line);
      singleInst << line << endl;
      if (line == "% SZS end BatchProblems") {
	ready = true;
	break;
      }
    }
    if (!ready) {
      break;
    }
    CLTBMode ltbm;
    vistringstream childInp(singleInst.str());
    ltbm.solveBatch(childInp);
  }
} // CLTBMode::perform

/**
 * This function processes a single batch in a batch file. It makes the following
 * steps: 
 * <ol><li>read the batch file</li>
 * <li>load the common axioms and put them into a SInE selector</li>
 * <li>spawn child processes that try to prove a problem by calling
 *     CLTBProblem::searchForProof(). These processes are run sequentially and the time
 *     limit for each one is computed depending on the per-problem time limit,
 *     batch time limit, and time spent on this batch so far. The termination
 *     time for the proof search for a problem will be passed to
 *     CLTBProblem::searchForProof() as an argument.</li></ol>
 * @author Andrei Voronkov
 * @since 04/06/2013 flight Manchester-Frankfurt
 */
void CLTBMode::solveBatch(istream& batchFile)
{
  CALL("CLTBMode::solveBatch(istream& batchfile)");

  // this is the time in milliseconds since the start when this batch file should terminate
  _timeUsedByPreviousBatches = env.timer->elapsedMilliseconds();
  coutLineOutput() << "Starting Vampire on the batch file " << "\n";
  int terminationTime = readInput(batchFile);
  loadIncludes();

  doTraining();

  int solvedProblems = 0;
  int remainingProblems = problemFiles.size();
  StringPairStack::BottomFirstIterator probs(problemFiles);
  while (probs.hasNext()) {
    StringPair res=probs.next();

    vstring probFile=res.first;
    vstring outFile=res.second;

    // calculate the next problem time limit in milliseconds
    int elapsedTime = env.timer->elapsedMilliseconds();
    int timeRemainingForThisBatch = terminationTime - elapsedTime;
    coutLineOutput() << "time remaining for this batch " << timeRemainingForThisBatch << endl;
    int remainingBatchTimeForThisProblem = timeRemainingForThisBatch / remainingProblems;
    coutLineOutput() << "remaining batch time for this problem " << remainingBatchTimeForThisProblem << endl;
    int nextProblemTimeLimit;
    if (!_problemTimeLimit) {
      nextProblemTimeLimit = remainingBatchTimeForThisProblem;
    }
    else if (remainingBatchTimeForThisProblem > _problemTimeLimit) {
      nextProblemTimeLimit = _problemTimeLimit;
    }
    else {
      nextProblemTimeLimit = remainingBatchTimeForThisProblem;
    }
    // time in milliseconds when the current problem should terminate
    int problemTerminationTime = elapsedTime + nextProblemTimeLimit;
    coutLineOutput() << "problem termination time " << problemTerminationTime << endl;

    env.beginOutput();
    env.out() << flush << "%" << endl;
    lineOutput() << "SZS status Started for " << probFile << endl << flush;
    env.endOutput();

    pid_t child = Multiprocessing::instance()->fork();
    if (!child) {
      // child process
      CLTBProblem prob(this, probFile, outFile);
      try {
        prob.searchForProof(problemTerminationTime);
      } catch (Exception& exc) {
        cerr << "% Exception at proof search level" << endl;
        exc.cry(cerr);
        System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
      }
      // searchForProof() function should never return
      ASSERTION_VIOLATION;
    }

    env.beginOutput();
    lineOutput() << "solver pid " << child << endl;
    env.endOutput();
    int resValue;
    // wait until the child terminates
    try {
      pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
      ASS_EQ(finishedChild, child);
    }
    catch(SystemFailException& ex) {
      cerr << "% SystemFailException at batch level" << endl;
      ex.cry(cerr);
    }

    // output the result depending on the termination code
    env.beginOutput();
    if (!resValue) {
      lineOutput() << "SZS status Theorem for " << probFile << endl;
      solvedProblems++;
    }
    else {
      lineOutput() << "SZS status GaveUp for " << probFile << endl;
    }
    env.out() << flush << '%' << endl;
    lineOutput() << "% SZS status Ended for " << probFile << endl << flush;
    env.endOutput();

    Timer::syncClock();

    remainingProblems--;
  }
  env.beginOutput();
  lineOutput() << "Solved " << solvedProblems << " out of " << problemFiles.size() << endl;
  env.endOutput();
} // CLTBMode::solveBatch(batchFile)

void CLTBMode::loadIncludes()
{
  CALL("CLTBMode::loadIncludes");

  UnitList* theoryAxioms=0;
  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    StringList::Iterator iit(_theoryIncludes);
    while (iit.hasNext()) {
      vstring fname=env.options->includeFileName(iit.next());

      ifstream inp(fname.c_str());
      if (inp.fail()) {
        USER_ERROR("Cannot open included file: "+fname);
      }
      Parse::TPTP parser(inp);
      parser.parse();
      UnitList* funits = parser.units();
      if (parser.containsConjecture()) {
	USER_ERROR("Axiom file " + fname + " contains a conjecture.");
      }

      UnitList::Iterator fuit(funits);
      while (fuit.hasNext()) {
	fuit.next()->markIncluded();
      }
      theoryAxioms=UnitList::concat(funits,theoryAxioms);
    }
  }

  _baseProblem = new Problem(theoryAxioms);
  //ensure we scan the theory axioms for property here, so we don't need to
  //do it afterward in each problem
  _baseProblem->getProperty();
  env.statistics->phase=Statistics::UNKNOWN_PHASE;
} // CLTBMode::loadIncludes

void CLTBMode::doTraining()
{
  CALL("CLTBMode::doTraining");

  Stack<vstring> solutions;
  System::readDir(trainingDirectory+"/Solutions",solutions);

  ScopedPtr<DHMap<Unit*,Parse::TPTP::SourceRecord*> > sources;
  sources = new DHMap<Unit*,Parse::TPTP::SourceRecord*>();

  Stack<vstring>::Iterator it(solutions);
  while (it.hasNext()) {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    vstring& solnFileName = it.next();

    cout << "Reading solutions " << solnFileName << endl;

    ifstream soln(solnFileName.c_str());
    if (soln.fail()) {
      USER_ERROR("Cannot open problem file: " + solnFileName);
    }
    Parse::TPTP parser(soln);
    parser.setUnitSourceMap(sources.ptr());
    parser.parse();
    UnitList* solnUnits = parser.units();


    UnitList::Iterator it(solnUnits);
    while (it.hasNext()) {
      Unit* unit = it.next();
      cout << unit->toString() << endl;
    }
  }

  // Idea is to solve training problems and look in proofs for common clauses derived from axioms
  // these can then be loaded into later proof attempts with weight zero to ensure they are processed quickly 
  //
  // training could insert these axioms directly into the base problem object and mark their input type such that
  // they get weight zero in Vampire
  //
  // do to training let's
  // prove the training problems in the same way as the real problems - this will write output to a file per problem
  // this output should contain the proofs
  // read in these files and parse the proofs, building up the clauses to add to the base problem
  // add clauses to the base problem

} // CLTBMode::doTraining

/**
 * Read a single batch file from @b in. Return the time in milliseconds since
 * the start, when the process should terminate. If the batch contains no overall
 * time limit, return a very large integer value.
 * Set _problemTimeLimit to the per-problem time limit from
 * the batch file.
 * @since 04/06/2013 flight Manchester-Frankfurt
 * @author Andrei Voronkov
 */
int CLTBMode::readInput(istream& in)
{
  CALL("CLTBMode::readInput");

  // ignore any lines describing the division or the category
  // apart from the training directory
  vstring line, word;

  getline(in,line);
  while (line.find("division.category") != vstring::npos){
    // Get training directory
    if(line.find("training_directory") != vstring::npos){
      StringStack ls;
      StringUtils::splitStr(line.c_str(),' ',ls);
      trainingDirectory = ls[1];
    }
    getline(in,line);
  }

  if (line!="% SZS start BatchConfiguration") {
    USER_ERROR("\"% SZS start BatchConfiguration\" expected, \""+line+"\" found.");
  }

  getline(in, line);

  _questionAnswering = false;
  _problemTimeLimit = -1;
  int batchTimeLimit = -1;
  category = "";

  StringStack lineSegments;
  while (!in.eof() && line!="% SZS end BatchConfiguration") {
    lineSegments.reset();
    StringUtils::splitStr(line.c_str(), ' ', lineSegments);
    vstring param = lineSegments[0];
    if (param == "division.category") {
      if (lineSegments.size()!=2) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }
      category = lineSegments[1];      
    }
    else if (param == "output.required" || param == "output.desired") {
      if (lineSegments.find("Answer")) {
	_questionAnswering = true;
      }
    }
    else if (param == "execution.order") {
      // we ignore this for now and always execute in order
    }
    else if (param == "limit.time.problem.wc") {
      if (lineSegments.size() != 2 ||
	  !Int::stringToInt(lineSegments[1], _problemTimeLimit)) {
	USER_ERROR("unexpected \""+param+"\" specification: \""+line+"\"");
      }      
      _problemTimeLimit = 1000 * _problemTimeLimit;
    }
    else if (param == "limit.time.overall.wc") {
      if (lineSegments.size() != 2 ||
	  !Int::stringToInt(lineSegments[1], batchTimeLimit)) {
	USER_ERROR("unexpected \"" + param + "\" specification: \""+ line +"\"");
      }
      batchTimeLimit = 1000 * batchTimeLimit;
    }
    else {
      USER_ERROR("unknown batch configuration parameter: \""+line+"\"");
    }

    getline(in, line);
  }

  if (line != "% SZS end BatchConfiguration") {
    USER_ERROR("\"% SZS end BatchConfiguration\" expected, \"" + line + "\" found.");
  }
  if (_questionAnswering) {
    env.options->setQuestionAnswering(Options::QuestionAnsweringMode::ANSWER_LITERAL);
  }

  getline(in, line);
  if (line!="% SZS start BatchIncludes") {
    USER_ERROR("\"% SZS start BatchIncludes\" expected, \""+line+"\" found.");
  }

  _theoryIncludes=0;
  for (getline(in, line); line[0]!='%' && !in.eof(); getline(in, line)) {
    size_t first=line.find_first_of('\'');
    size_t last=line.find_last_of('\'');
    if (first == vstring::npos || first == last) {
      USER_ERROR("Include specification must contain the file name enclosed in the ' characters:\""+line+"\".");
    }
    ASS_G(last,first);
    vstring fname=line.substr(first+1, last-first-1);
    StringList::push(fname, _theoryIncludes);
  }

  while (!in.eof() && line == "") { getline(in, line); }
  if (line!="% SZS end BatchIncludes") {
    USER_ERROR("\"% SZS end BatchIncludes\" expected, \""+line+"\" found.");
  }
  getline(in, line);
  if (line!="% SZS start BatchProblems") {
    USER_ERROR("\"% SZS start BatchProblems\" expected, \""+line+"\" found.");
  }

  for (getline(in, line); line[0]!='%' && !in.eof(); getline(in, line)) {
    size_t spc=line.find(' ');
    size_t lastSpc=line.find(' ', spc+1);
    if (spc == vstring::npos || spc == 0 || spc == line.length()-1) {
      USER_ERROR("Two file names separated by a single space expected:\""+line+"\".");
    }
    vstring inp=line.substr(0,spc);
    vstring outp=line.substr(spc+1, lastSpc-spc-1);
    problemFiles.push(make_pair(inp, outp));
  }

  while (!in.eof() && line == "") {
    getline(in, line);
  }
  if (line!="% SZS end BatchProblems") {
    USER_ERROR("\"% SZS end BatchProblems\" expected, \""+line+"\" found.");
  }

  if (batchTimeLimit == -1) { // batch time limit is undefined
    if (_problemTimeLimit == -1) {
      USER_ERROR("either the problem time limit or the batch time limit must be specified");
    }
    // to avoid overflows when added to the current elapsed time, make it less than INT_MAX
    return INT_MAX / 8;
  }

  // batch time limit is defined
  if (_problemTimeLimit == -1) {
    _problemTimeLimit = 0;
  }
  return _timeUsedByPreviousBatches + batchTimeLimit;
} // CLTBMode::readInput

vstring CLTBProblem::problemFinishedString = "##Problem finished##vn;3-d-ca-12=1;'";

CLTBProblem::CLTBProblem(CLTBMode* parent, vstring problemFile, vstring outFile)
  : parent(parent), problemFile(problemFile), outFile(outFile),
    prb(*parent->_baseProblem)
{
}

/**
 * This function solves a single problem. It makes the following steps:
 * <ol><li>find the main and the fallback schedules depending on the problem
 *          properties</li>
 *     <li>run the main schedule using runSchedule()</li>
 *     <li>if the proof is not found, checks if all the remaining time
 *         was used: if not, it runs the fallback strategy using
 *         runSchedule() with the updated time limit</li></ol>
 * Once the problem is proved, the runSchedule() function does not return
 * and the process terminates.
 *
 * If a slice contains sine_selection value different from off, theory axioms
 * will be selected using SInE from the common axioms included in the batch file
 * (all problem axioms, including the included ones, will be used as a base
 * for this selection).
 *
 * If the sine_selection is off, all the common axioms will be just added to the
 * problem axioms. All this is done in the @b runSlice(Options&) function.
 * @param terminationTime the time in milliseconds since the prover starts when
 *        the strategy should terminate
 * @author Krystof Hoder
 * @since 04/06/2013 flight Frankfurt-Vienna, updated for CASC-J6
 * @author Andrei Voronkov
 */
void CLTBProblem::performStrategy(int terminationTime)
{
  CALL("CLTBProblem::performStrategy");

  Property& property = *prb.getProperty();

  Property::Category cat = property.category();
  unsigned atoms = property.atoms();
  unsigned prop = property.props();
  cout << "% Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  Schedule quick;
  // Schedule fallback;

  switch (cat) {
  case Property::NEQ:
    if (prop == 131079) {
      quick.push("dis+11_4:1_bs=off:cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_8");
      quick.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=2.5:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_12");
      quick.push("dis+11_2_bs=off:bsr=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:sio=off:spl=sat:sser=off:ssnc=none_23");
      quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_5");
      quick.push("dis+11_4_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=1.7:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_68");
      quick.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_36");
      quick.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_29");
      quick.push("dis+1011_24_cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_120");
      quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_117");
      quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_18");
      quick.push("ott+1011_3_bs=off:bsr=unit_only:fde=none:nwc=2:sio=off:spl=sat:ssfq=1.0:ssnc=none_55");
      quick.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_228");
      quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_283");
      quick.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_480");
      quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_44");
      quick.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_110");
    }
    else if (prop == 1) {
      if (atoms > 175) {
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_1");
	quick.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_2");
	quick.push("dis-1010_3:1_bs=off:drc=off:ep=RS:flr=on:nwc=5:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_38");
	quick.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_29");
	quick.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_57");
	quick.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_26");
	quick.push("dis-1002_2:3_bs=off:drc=off:gsp=input_only:nwc=1.7:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=occurrence_3");
	quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_1");
	quick.push("dis-11_28_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none_48");
	quick.push("ott-11_40_bd=off:bs=off:drc=off:flr=on:fsr=off:lcm=predicate:nwc=10:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:updr=off_42");
	quick.push("ott+1_3:1_bs=off:br=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=occurrence:urr=on_11");
	quick.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_56");
	quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_33");
	quick.push("dis+10_1024_bs=off:drc=off:flr=on:fsr=off:nwc=1.1:sio=off:spl=sat:ssfq=1.4:ssnc=none_76");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_65");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_72");
	quick.push("lrs+2_64_bd=off:bs=off:br=off:cond=on:drc=off:flr=on:fde=none:nwc=1.7:stl=30:sio=off:spl=sat:ssfp=1000:ssfq=1.4:ssnc=none:urr=on_54");
	quick.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:stl=60:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_211");
	quick.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_171");
	quick.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_1");
	quick.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_16");
	quick.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_101");
      }
      else {
	quick.push("dis+3_4_bs=off:br=off:cond=on:drc=off:ep=RSTC:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on_2");
	quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_15");
	quick.push("ins+1_3:1_bs=off:cond=on:ep=RSTC:flr=on:gs=on:igbrr=0.8:igrr=1/4:igrp=400:igrpq=1.1:igwr=on:nwc=1.5:sio=off:urr=on_4");
	quick.push("dis+1011_1024_bs=unit_only:drc=off:gsp=input_only:nwc=1.1:sio=off:spo=on:urr=on_10");
	quick.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_4");
	quick.push("dis+11_3:1_bs=off:cond=fast:drc=off:nwc=5:sio=off:spl=sat:sser=off:ssnc=none_17");
	quick.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:sio=off:spl=sat:ssnc=none_21");
	quick.push("lrs+2_14_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:nwc=1.1:stl=30:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_227");
	quick.push("lrs+4_24_bd=off:bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:stl=60:sio=off:spl=sat:ssfp=4000:ssfq=1.2:ssnc=none_540");
	quick.push("ott+10_64_bd=off:bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_212");
	quick.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_46");
      }
    }
    else if (prop == 3) {
      if (atoms <= 2000) {
	quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:ep=on:nwc=10:nicw=on:sio=off:spl=sat:ssnc=none:urr=on_8");
	quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_95");
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_23");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_2");
	quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_69");
	quick.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_20");
	quick.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_5");
	quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_1");
	quick.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_46");
	quick.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_25");
	quick.push("ott+10_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:ssfq=2.0:ssnc=none_91");
	quick.push("lrs+10_1_bs=off:cond=fast:nwc=5:stl=20:sio=off:spl=sat:ssfq=1.1:ssnc=none_4");
	quick.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_50");
	quick.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_48");
	quick.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_96");
	quick.push("dis+1011_2_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_202");
	quick.push("lrs+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:stl=30:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off:sp=reverse_arity_96");
	quick.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_256");
	quick.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_140");
	quick.push("dis+2_4:1_bs=unit_only:cond=on:flr=on:lcm=predicate:nwc=1:ssac=none:ssfp=100000:ssfq=2.0:ssnc=all:sfv=off:urr=on_257");
	quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_106");
      }
      else {
	quick.push("dis-1010_3:1_bs=off:drc=off:ep=RS:flr=on:nwc=5:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_3");
	quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_27");
	quick.push("dis+10_10_bs=off:cond=fast:drc=off:gs=on:nwc=1.7:nicw=on:sd=1:ss=axioms:st=3.0_2");
	quick.push("dis-1002_5:1_bs=off:cond=fast:drc=off:ep=on:nwc=1.1:sd=4:ss=axioms:sos=on:sio=off:spl=sat:urr=on_17");
	quick.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_14");
	quick.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_23");
	quick.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_2");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_31");
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_2");
	quick.push("dis+3_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=10:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=reverse_arity_17");
	quick.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=700:igrpq=1.5:igwr=on:nwc=3:sos=on:sgo=on:sio=off_70");
	quick.push("ott-1010_2:1_bs=off:cond=fast:drc=off:nwc=3:sd=1:ss=axioms:st=2.0:sio=off:spl=sat:sser=off:ssnc=none_36");
	quick.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_90");
	quick.push("ott+1_10_bd=off:bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_111");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_246");
	quick.push("lrs+2_3:1_bs=off:br=off:cond=fast:drc=off:flr=on:nwc=4:stl=60:sio=off:spo=on:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_250");
	quick.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:stl=60:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_549");
      }
    }
    else {
      quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_8");
      quick.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_6");
      quick.push("dis+11_8:1_bs=off:drc=off:ep=RS:nwc=10:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_2");
      quick.push("dis+2_2:3_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfq=1.1:ssnc=none:urr=on_7");
      quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_12");
      quick.push("dis+2_5_cond=fast:drc=off:fsr=off:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_9");
      quick.push("dis-1010_6_bs=off:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sos=all:sp=occurrence_13");
      quick.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_1");
      quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_4");
      quick.push("dis+11_24_bs=off:cond=fast:drc=off:nwc=2.5:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1");
      quick.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_19");
      quick.push("lrs-1010_3_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1.1:nicw=on:stl=30:sos=on:sac=on:sio=off_3");
      quick.push("dis+11_20_bs=off:cond=fast:fde=none:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_9");
      quick.push("lrs-1002_6_bs=off:bsr=unit_only:cond=fast:fde=none:gsp=input_only:lcm=reverse:nwc=1:stl=30:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_11");
      quick.push("dis-1002_3:2_bs=off:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_8");
      quick.push("lrs+1010_24_bd=off:bs=off:cond=on:drc=off:gsp=input_only:nwc=1.3:nicw=on:stl=10:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_18");
      quick.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_10");
      quick.push("dis-1002_12_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_1");
      quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_26");
      quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_30");
      quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_252");
      quick.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_240");
      quick.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_1");
      quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_26");
      quick.push("dis-1002_2:3_bs=off:drc=off:gsp=input_only:nwc=1.7:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=occurrence_60");
    }
    break;

  case Property::HEQ:
    if (prop == 2) {
      quick.push("dis+11_10_bs=off:drc=off:nwc=10:sos=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_3");
      quick.push("ott+11_128_bs=off:drc=off:gsp=input_only:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_626");
      quick.push("dis+11_5:4_bs=off:cond=fast:drc=off:fde=none:nwc=1:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=none:urr=on_164");
      quick.push("ins+2_64_bs=off:cond=on:drc=off:flr=on:fde=none:igbrr=0.1:igrr=1/16:igrpq=1.3:igwr=on:nwc=1.7:sp=reverse_arity_1061");
    }
    else if (prop == 8194) {
      quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:nwc=10:stl=60:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_487");
      quick.push("lrs+11_3:1_bs=unit_only:drc=off:fde=none:nwc=10:stl=60:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_128");
      quick.push("lrs+2_4_bs=off:cond=fast:drc=off:gsp=input_only:nwc=4:stl=90:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_335");
      quick.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:flr=on:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssnc=none_205");
    }
    else {
      quick.push("ott+11_24_bd=off:bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_2");
      quick.push("ins+11_64_bs=off:cond=on:drc=off:fde=none:igbrr=0.2:igrr=1/64:igrp=400:igrpq=1.05:igwr=on:nwc=1.2:sio=off_29");
      quick.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=10:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_2");
      quick.push("dis-1002_3_bs=off:cond=fast:drc=off:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_2");
      quick.push("dis+10_1024_bd=off:bs=off:cond=on:drc=off:fde=none:nwc=2.5:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_162");
      quick.push("lrs-1_2_bs=off:drc=off:nwc=4:nicw=on:stl=30:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_236");
      quick.push("ins+4_5:4_bs=off:br=off:cond=on:ep=RSTC:flr=on:fsr=off:igbrr=0.1:igrr=1/16:igrpq=1.0:igwr=on:nwc=2:urr=on_323");
      quick.push("ott+11_24_bs=unit_only:cond=fast:drc=off:nwc=3:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_473");
    }
    break;
    
  case Property::PEQ:
    if (prop == 0) {
      if (atoms <= 15) {
	quick.push("dis+10_1024_bs=unit_only:cond=on:drc=off:nwc=1:sio=off:spl=sat:ssfq=1.0:ssnc=none_35");
	quick.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:stl=150:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_490");
	quick.push("lrs+4_14_cond=on:drc=off:flr=on:nwc=3:stl=180:spl=sat:sser=off:ssnc=none_947");
      }
      else {
	quick.push("dis-1010_14_bs=off:drc=off:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_12");
	quick.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_241");
	quick.push("ott+11_5_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_753");
	quick.push("ott+11_2:3_bd=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:updr=off_243");
	quick.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_441");
      }
    }
    else if (prop == 1) {
      quick.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:stl=30:sac=on:sio=off_14");
      quick.push("dis-1003_128_drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_40");
      quick.push("lrs+3_40_bs=unit_only:bsr=on:cond=on:drc=off:fsr=off:nwc=1.1:nicw=on:stl=100:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on:updr=off_645");
      quick.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_115");
      quick.push("dis+1_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_278");
      quick.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_544");
      quick.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:stl=150:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1006");
    }
    else {
      quick.push("dis-1010_14_bs=off:drc=off:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_18");
      quick.push("ott+3_4:1_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence:urr=on_13");
      quick.push("lrs+3_16_bsr=unit_only:cond=on:drc=off:fsr=off:nwc=4:stl=150:sio=off:spl=sat:ssnc=none:urr=on_141");
      quick.push("lrs+10_2:3_bd=off:cond=on:drc=off:flr=on:nwc=5:nicw=on:stl=90:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_85");
      quick.push("dis-1004_1024_bs=off:cond=fast:drc=off:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none_72");
      quick.push("ott+11_3_bd=off:bs=unit_only:bsr=unit_only:drc=off:fsr=off:nwc=1.5:sio=off:spo=on:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none_39");
      quick.push("ott+2_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_116");
      quick.push("ott-1003_8_bs=off:bsr=on:cond=on:drc=off:fsr=off:gs=on:nwc=5:sac=on:sio=off:sp=occurrence_156");
      quick.push("ins+1_20_bsr=on:br=off:cond=fast:drc=off:fsr=off:fde=none:igbrr=0.3:igrr=1/32:igrp=4000:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.2:sgo=on:sio=off:sp=occurrence:urr=on_159");
      quick.push("ott+3_128_bs=off:drc=off:nwc=1.1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_321");
    }
    break;

  case Property::HNE:
    if (prop == 8192) {
      if (atoms > 6) {
	quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_76");
	quick.push("dis-1004_5:1_bs=off:cond=on:nwc=2:sio=off_17");
	quick.push("dis+11_2:3_bs=off:cond=fast:fsr=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_125");
	quick.push("ott+1011_10_bs=off:cond=on:nwc=3:sio=off:spl=sat:ssnc=none_61");
	quick.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:stl=90:sio=off:spo=on_127");
	quick.push("ott+1003_28_bs=off:cond=on:flr=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=off_275");
	quick.push("dis+2_5:4_cond=fast:flr=on:lcm=predicate:nwc=1.5:sio=off:spl=off_562");
	quick.push("dis+1002_64_bs=off:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:nicw=on:sio=off:spo=on_391");
	quick.push("lrs+10_8:1_bs=off:cond=fast:flr=on:fsr=off:nwc=2.5:stl=90:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_601");
      }
      else {
	quick.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_103");
	quick.push("lrs+3_4_bs=off:cond=fast:flr=on:nwc=1:nicw=on:stl=30:sio=off:spl=sat:ssnc=none_172");
	quick.push("lrs+11_128_cond=fast:lcm=reverse:nwc=1.5:nicw=on:stl=60:sio=off:spl=sat:ssfp=100000:ssfq=2.0:ssnc=none_525");
	quick.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:stl=180:sio=off:spl=sat:ssfq=2.0_611");
      }
    }
    else {
      quick.push("dis+1011_14_bs=off:nwc=4:sio=off:spl=off_2");
      quick.push("dis+10_3_bs=off:br=off:cond=fast:gs=on:nwc=1:sos=all:sio=off:urr=on_22");
      quick.push("ott+1011_10_bs=off:cond=on:nwc=3:sio=off:spl=sat:ssnc=none_14");
      quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_1");
      quick.push("ott+1011_20_bs=off:cond=fast:nwc=5:sio=off:spl=off_7");
      quick.push("lrs+10_3:1_bs=off:cond=on:flr=on:nwc=10:stl=50:sio=off:spl=off:sp=reverse_arity_62");
      quick.push("ott+1_8:1_bs=off:cond=on:gs=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssnc=none_178");
      quick.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:stl=90:sio=off:spo=on_16");
      quick.push("ott+1011_10_bs=off:cond=fast:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_21");
    }
    break;

  case Property::NNE:
    quick.push("dis+1011_50_bs=off:cond=fast:flr=on:gsp=input_only:nwc=1.3:sos=all_102");
    quick.push("dis-1010_14_bsr=on:cond=on:nwc=1.5:sio=off:spl=sat:ssfp=100000:ssfq=1.1:ssnc=none_69");
    quick.push("dis+11_20_bs=off:fsr=off:gsp=input_only:lcm=reverse:nwc=1.3:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_13");
    quick.push("dis-2_16_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:sagn=off:sio=off:spl=sat:ssnc=none_50");
    quick.push("ott+1011_5_bs=off:gs=on:nwc=2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssnc=none_33");
    quick.push("dis+1011_16_bs=unit_only:cond=on:fsr=off:gsp=input_only:nwc=1.7:sos=all:sgo=on:sio=off:spl=sat:ssfq=2.0:ssnc=all_60");
    quick.push("ott-1002_1024_cond=on:flr=on:gs=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none:urr=on_42");
    quick.push("dis+1011_12_bs=off:cond=fast:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_778");
    quick.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_216");
    quick.push("dis+1011_40_bs=off:gsp=input_only:nwc=4:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_146");
    quick.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:sio=off:spl=sat:ssnc=none_176");
    quick.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none_217");
    break;

  case Property::FEQ:
    if (prop == 131075) {
      if (atoms > 3000) {
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_19");
	quick.push("ins+1011_6_bs=off:bsr=unit_only:cond=on:ep=RSTC:fde=none:igbrr=0.2:igrr=8/1:igrp=1400:igrpq=1.5:igwr=on:nwc=1.1:sos=on_15");
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_15");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_63");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_15");
	quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_41");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_89");
	quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_223");
	quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_737");
	quick.push("ott+1011_2:3_bs=off:br=off:cond=on:drc=off:gs=on:nwc=10:sd=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_11");
      }
      else {
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_1");
	quick.push("dis+11_28_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=5:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sp=occurrence_10");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_1");
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_35");
	quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_75");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_21");
	quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_4");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_30");
	quick.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:stl=120:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_8");
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_179");
	quick.push("dis+1011_10_bd=off:bs=off:drc=off:ep=RS:fsr=off:nwc=1:nicw=on_8");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_182");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_167");
	quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_92");
	quick.push("lrs-1004_32_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:lcm=reverse:nwc=1:nicw=on:stl=30:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_132");
	quick.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_144");
	quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_291");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_298");
      }
    }
    else if (prop == 1) {
      if (atoms > 125) {
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_8");
	quick.push("ott+11_50_bs=off:cond=on:drc=off:fde=none:lcm=reverse:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_7");
	quick.push("ins+11_3:1_bd=off:bs=off:cond=fast:drc=off:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:lcm=predicate:nwc=1:sos=all:sp=occurrence_1");
	quick.push("ott-1003_24_drc=off:nwc=2:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_2");
	quick.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_1");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_190");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_10");
	quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_54");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_168");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_80");
	quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_198");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_12");
      }
      else {
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_13");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_3");
	quick.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_3");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_3");
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_6");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_1");
	quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_8");
	quick.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_23");
	quick.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_114");
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_121");
	quick.push("ott+1_2:3_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_197");
	quick.push("ott+4_64_bd=off:bs=off:br=off:cond=on:drc=off:fsr=off:gs=on:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:urr=on_795");
      }
    }
    else if (prop == 0) {
      if (atoms < 8) {
      quick.push("ott+10_4_bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_1");
      quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_424");
      quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_1841");
      }
      else if (atoms < 12) {
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_774");
      }
      else if (atoms < 15) {
	quick.push("lrs-1004_12_bs=off:bsr=unit_only:drc=off:nwc=1.7:nicw=on:stl=60:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none_473");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_1806");
      }
      else if (atoms < 50) {
	quick.push("dis+4_5_bs=off:drc=off:lcm=reverse:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=occurrence_2");
	quick.push("ott+3_7_bs=off:cond=fast:nwc=3:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sio=off:spl=sat_4");
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_33");
	quick.push("lrs-1_10_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:stl=20:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_127");
	quick.push("ins+4_2_bd=off:bs=off:gs=on:igbrr=0.8:igrr=1/32:igrp=2000:igrpq=1.2:igwr=on:lcm=reverse:nwc=10:urr=on_3");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_126");
	quick.push("ott-3_10_bs=off:br=off:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_66");
	quick.push("ins-11_3:1_bs=off:cond=on:drc=off:fsr=off:igbrr=0.5:igrp=100:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.1:sos=all:sio=off:spl=off:sp=reverse_arity_12");
	quick.push("dis+4_2:1_bs=off:br=off:drc=off:fsr=off:nwc=1:sos=all:sio=off:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_148");
	quick.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:stl=30:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_132");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_354");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_220");
	quick.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:stl=120:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_569");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_1");
	quick.push("ott-1003_24_drc=off:nwc=2:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_46");
      }
      else if (atoms < 150) {
	quick.push("ott+10_3:1_bsr=unit_only:cond=fast:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on:updr=off_23");
	quick.push("ott+4_32_bs=off:flr=on:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_272");
	quick.push("lrs-2_6_bs=off:cond=fast:drc=off:nwc=4:nicw=on:stl=30:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_4");
	quick.push("ott+10_24_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssnc=none_288");
	quick.push("dis+2_20_drc=off:ep=RST:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_62");
	quick.push("dis+4_40_cond=on:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_149");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_77");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_551");
      }
      else if (atoms < 900) {
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_30");
	quick.push("dis+1011_3_bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_71");
	quick.push("dis-1010_4:1_bs=off:drc=off:lcm=predicate:nwc=2:nicw=on:sio=off_165");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_498");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_929");
      }
      else {
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_20");
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_55");
	quick.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_127");
	quick.push("dis+4_10_bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none_274");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_560");
	quick.push("dis-1010_3:1_bd=off:bs=off:cond=fast:gs=on:lcm=reverse:nwc=1.1:sac=on_505");
      }
    }
    else if (prop == 131087) {
      if (atoms > 140000) {
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_23");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_98");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_39");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_43");
	quick.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_22");
	quick.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_20");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_134");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_95");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_24");
	quick.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_16");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_136");
	quick.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_33");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_51");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_42");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_47");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_168");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_129");
	quick.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_213");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_111");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_121");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_149");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_305");
      }
      else if (atoms > 70000) {
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_13");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_16");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_17");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_19");
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_9");
	quick.push("dis-1002_40_bs=off:ep=RST:flr=on:gs=on:lcm=predicate:nwc=2.5:nicw=on:sd=5:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:ssnc=none:sp=reverse_arity_8");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_40");
	quick.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_37");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_64");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_86");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_9");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_87");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_19");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_63");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_103");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_135");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_276");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_76");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_104");
	quick.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_122");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_275");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_142");
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_11");
      }
      else if (atoms > 3200) {
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_8");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_3");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_21");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_10");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_40");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_47");
	quick.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_7");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_3");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_55");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_5");
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_10");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_36");
	quick.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_13");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_28");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_141");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:lcm=predicate:nwc=10:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_24");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_21");
	quick.push("ott+2_4:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:sd=3:ss=axioms:sos=on:spl=sat:urr=on_23");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_53");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_259");
	quick.push("dis+1_14_bd=off:bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=4:sos=on:sio=off:spo=on:sp=reverse_arity_114");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_175");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.5:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=reverse_arity_179");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_8");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_102");
      }
      else if (atoms > 2200) {
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_22");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_5");
	quick.push("ott+1011_2:1_bs=off:cond=fast:drc=off:nwc=1:nicw=on:sos=all:sio=off:spo=on_29");
	quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_104");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_205");
	quick.push("lrs-11_12_bs=off:drc=off:fde=none:gsp=input_only:gs=on:lcm=predicate:nwc=4:nicw=on:stl=300:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sfv=off:sp=occurrence:urr=on:updr=off_1612");
      }
      else if (atoms > 900) {
	quick.push("lrs+1_5_bs=off:cond=fast:drc=off:flr=on:nwc=10:stl=30:sac=on:sio=off:urr=on_6");
	quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_40");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_2");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_47");
	quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_58");
	quick.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_424");
	quick.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_249");
	quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_287");
	quick.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_325");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:lcm=predicate:nwc=10:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_7");
	quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_36");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_86");
      }
      else {
	quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_7");
	quick.push("dis+2_2:3_bs=off:bsr=unit_only:cond=fast:drc=off:ep=RS:lcm=reverse:nwc=1.2:sos=all:sio=off:spl=sat:ssfp=4000:ssfq=1.4:ssnc=none:sfv=off:sp=occurrence_24");
	quick.push("dis+1010_40_bs=off:drc=off:ep=RS:nwc=1:sio=off:spo=on:spl=sat:ssnc=none_21");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_17");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_23");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_9");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_3");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_272");
	quick.push("dis-1010_5:4_bs=off:bsr=on:cond=fast:drc=off:fde=none:gsp=input_only:nwc=3:sgo=on:sio=off:sp=occurrence:urr=on_150");
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_220");
	quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_351");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_18");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=reverse:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_85");
      }
    }
    else if (prop == 131073) {
      if (atoms > 400) {
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_2");
	quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_11");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_12");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_2");
	quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_4");
	quick.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_3");
	quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_26");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_2");
	quick.push("dis+4_5_bs=off:drc=off:lcm=reverse:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=occurrence_7");
	quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_2");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_12");
	quick.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_14");
	quick.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:sio=off:spl=sat:urr=on_3");
	quick.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_24");
	quick.push("ott-1010_2:3_bs=off:cond=fast:drc=off:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_9");
	quick.push("dis+1010_32_cond=fast:drc=off:ep=RS:fsr=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_66");
	quick.push("lrs-1002_3_bd=off:bs=off:drc=off:ep=on:nwc=1.7:stl=150:sos=on:sac=on:sio=off_21");
	quick.push("tab+10_1_ep=RST:gsp=input_only:sd=4:ss=axioms:st=2.0:sio=off:tbsr=off:tgawr=1/32:tglr=1/5:tipr=off:tlawr=8/1_73");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_183");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_122");
	quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_28");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_32");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_92");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_148");
	quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_1");
	quick.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_1");
	quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_2");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_4");
	quick.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_5");
	quick.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_8");
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_13");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_13");
	quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_20");
      }
      else if (atoms > 150) {
	quick.push("ott-1010_2:3_bs=off:cond=fast:drc=off:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_5");
	quick.push("dis+10_24_bs=off:br=off:drc=off:nwc=4:sd=5:ss=axioms:st=1.5:sgo=on:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all:urr=on_1");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_20");
	quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_25");
	quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_1");
	quick.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_27");
	quick.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:stl=30:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_11");
	quick.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_68");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_19");
	quick.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_146");
	quick.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_33");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1.3:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:spl=sat:sser=off_72");
	quick.push("ott+1_2:3_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_20");
	quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_242");
	quick.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_189");
	quick.push("dis+2_16_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none_420");
	quick.push("ott+1011_2_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_227");
	quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_231");
	quick.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_1");
	quick.push("ott+1011_2:1_bs=off:cond=fast:drc=off:nwc=1:nicw=on:sos=all:sio=off:spo=on_23");
      }
      else {
	quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_1");
	quick.push("dis-1002_6_bs=off:drc=off:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat:sser=off_1");
	quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_4");
	quick.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_25");
	quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_1");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_97");
	quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_8");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_18");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_860");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_26");
	quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_262");
      }
    }
    else if (prop == 2) {
      if (atoms > 25) {
	quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_16");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_874");
	quick.push("lrs+1_64_bs=off:drc=off:gsp=input_only:nwc=1.7:nicw=on:stl=60:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:updr=off_282");
	quick.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_368");
      }
      else {
	quick.push("ins+3_10_bs=off:drc=off:fde=none:igbrr=0.8:igrr=1/128:igrp=100:igrpq=1.0:igwr=on:nwc=2.5:sio=off:spl=off_152");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_48");
	quick.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_245");
	quick.push("ott+11_24_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=reverse_arity_178");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_577");
	quick.push("ott+4_14_bs=unit_only:cond=fast:drc=off:nwc=1.2:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_383");
	quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_73");
	quick.push("lrs+10_20_bs=off:cond=on:drc=off:gs=on:nwc=1.1:stl=10:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_80");
      }
    }
    else if (prop == 131072) {
      quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_16");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_90");
      quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_1");
      quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_7");
      quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_16");
      quick.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_105");
      quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_110");
      quick.push("dis+1003_1024_bs=off:drc=off:fsr=off:nwc=1.7:nicw=on:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_38");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_59");
      quick.push("ott+10_3:1_bd=off:drc=off:lcm=reverse:nwc=10:nicw=on:sio=off:spo=on:ssac=none:sscc=on:sser=off:ssfp=1000:ssfq=1.2:ssnc=all_667");
      quick.push("dis-1010_50_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_580");
      quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_12");
    }
    else if (atoms > 10000) {
      quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_24");
      quick.push("dis+2_10_bs=off:cond=fast:ep=RST:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_44");
      quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_33");
      quick.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_35");
      quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_6");
      quick.push("dis+1_10_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=7:ss=axioms:st=1.5:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_153");
      quick.push("dis+11_10_bs=off:lcm=predicate:nwc=1.3:sio=off_100");
      quick.push("dis+11_1024_bsr=unit_only:cond=fast:nwc=1.3:sio=off:spl=off_590");
      quick.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_217");
      quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_244");
    }
    else if (prop == 131083) {
      quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_1");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_6");
      quick.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_2");
      quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_187");
      quick.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_441");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_474");
    }
    else if (prop == 131074) {
      quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_2");
      quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_23");
      quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_4");
      quick.push("dis+10_2_bs=off:cond=on:drc=off:fde=none:lcm=predicate:nwc=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=reverse_arity_31");
      quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_75");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_236");
      quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_27");
      quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_56");
      quick.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_157");
    }
    else {
      quick.push("ott+1011_10_bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_4");
      quick.push("ins+10_2:3_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=100:igrpq=1.0:igwr=on:nwc=2:sos=all:sio=off:urr=on_1");
      quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_9");
      quick.push("dis+4_5:1_bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ss=axioms:st=2.0:sac=on:sio=off:sp=occurrence:urr=on_3");
      quick.push("dis+11_2:3_bs=off:bsr=unit_only:drc=off:ep=R:lcm=reverse:nwc=2:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1");
      quick.push("dis+1011_28_cond=on:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_12");
      quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_1");
      quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_37");
      quick.push("ins+1011_8:1_bs=off:cond=fast:drc=off:ep=on:igbrr=0.1:igrr=1/4:igrpq=1.0:igwr=on:nwc=1.3:sos=all:sio=off:sfv=off:urr=on:updr=off_8");
      quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_1");
      quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_17");
      quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_7");
      quick.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_128");
      quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_40");
      quick.push("dis+11_1_bs=off:drc=off:ep=on:flr=on:lcm=predicate:nwc=5:nicw=on:ss=included:st=5.0:sos=all:sagn=off:spl=sat:sser=off:ssnc=none:updr=off_24");
      quick.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_9");
      quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_8");
      quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_10");
      quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_48");
      quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_12");
      quick.push("dis+10_24_bs=off:br=off:drc=off:nwc=4:sd=5:ss=axioms:st=1.5:sgo=on:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all:urr=on_7");
      quick.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_53");
      quick.push("dis-1002_8:1_bs=off:cond=on:drc=off:flr=on:gs=on:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_2");
      quick.push("ins+2_4:1_bs=off:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrpq=1.05:igwr=on:nwc=5:sos=on:sio=off:urr=on_1");
      quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_108");
      quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_165");
      quick.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_31");
      quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_23");
      quick.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_118");
      quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_296");
      quick.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_212");
      quick.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_164");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_14");
      quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_24");
    }
    break;

  case Property::FNE:
    if (atoms > 200) {
      quick.push("ins+10_1_gsp=input_only:igbrr=0.9:igrp=100:igrpq=1.1:nwc=2_5");
      quick.push("dis+11_50_bs=off:bsr=on:cond=on:lcm=reverse:nwc=1:sio=off:spl=sat:sser=off:ssnc=none:updr=off_267");
      quick.push("dis+4_128_bs=off:cond=on:flr=on:nwc=1.2:sos=on:sac=on_20");
      quick.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_59");
      quick.push("tab+10_1_spl=off:tbsr=off:tfsr=off:tgawr=3/1:tglr=1/20:tipr=off:tlawr=8/1_114");
      quick.push("dis+3_6_flr=on:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence_34");
      quick.push("ott+1011_50_bs=off:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on:updr=off_190");
      quick.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_354");
      quick.push("dis+1010_8_bs=off:nwc=1.1:sio=off_134");
      quick.push("dis+1004_10_bs=off:nwc=1.5:sagn=off:sio=off:spl=sat:ssnc=none_617");
    }
    else if (atoms > 120) {
      quick.push("ott-1002_3_bs=unit_only:bsr=unit_only:cond=on:gsp=input_only:nwc=1.2:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:urr=on_185");
      quick.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_204");
      quick.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:stl=120:spo=on_990");
    }
    else {
      quick.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_1");
      quick.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_1");
      quick.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:stl=120:spo=on_28");
      quick.push("ott+1_40_bsr=unit_only:cond=fast:gs=on:nwc=1.5:sio=off:spl=sat:ssnc=none:urr=on_102");
      quick.push("ins+10_1_igbrr=0.5:igrpq=1.2:nwc=1:sio=off_32");
      quick.push("ott+1_16_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=2.5_94");
      quick.push("ott-1010_128_bs=off:cond=on:lcm=predicate:nwc=1.3:urr=on_394");
      quick.push("ott+10_1024_bs=off:fsr=off:nwc=1.5:nicw=on:sio=off:spl=off_963");
    }
    break;
 
  case Property::EPR:
    if (prop == 131072) {
      quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_158");
      quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_162");
    }
    else if (atoms > 2000) {
      quick.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_119");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_1935");
    }
    else if (atoms > 1300) {
      quick.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_1");
      quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_148");
      quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_171");
      quick.push("ins+3_128_bs=off:br=off:drc=off:igbrr=0.1:igrr=32/1:igrp=2000:igrpq=2.0:igwr=on:nwc=3:sos=all:sio=off:urr=on_262");
      quick.push("ins+2_128_bs=unit_only:drc=off:fsr=off:igbrr=1.0:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:sos=on:sio=off:sp=occurrence_277");
      quick.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_560");
    }
    else if (atoms > 450) {
      quick.push("dis-10_5:4_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.1:sac=on:sio=off:spo=on_5");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_22");
      quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_56");
      quick.push("ins+3_50_bs=off:br=off:drc=off:igbrr=0.7:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=2:sp=occurrence:urr=on_501");
      quick.push("ins+10_1_igbrr=0.4:igrp=200:igrpq=1.5:nwc=1.1:sio=off_561");
    }
    else {
      quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_12");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_13");
      quick.push("ins+3_14_bs=off:cond=on:drc=off:flr=on:igbrr=0.2:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:nwc=1:urr=on_43");
      quick.push("ott+1_128_bs=off:cond=fast:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on_1");
      quick.push("dis+4_10_bs=off:drc=off:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.0:ssnc=none_482");
      quick.push("ins-10_14_bs=off:drc=off:fde=none:igbrr=0.9:igrr=1/4:igrp=2000:igrpq=2.0:igwr=on:nwc=1.5:sos=on:sgo=on:sio=off:updr=off_1506");
    }
    break;
 
  case Property::UEQ:
    if (prop == 2048) {
      quick.push("dis+2_14_bs=off:br=off:ep=RSTC:flr=on:fsr=off:nwc=2.5:nicw=on:sos=all:sio=off:spl=sat:ssnc=none:urr=on_2");
      quick.push("dis+10_32_bs=off:drc=off:fsr=off:nwc=5_2");
      quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_1097");
    }
    else if (prop == 2) {
      if (atoms <= 17) {
	quick.push("dis+11_16_bs=off:bfnt=on:fsr=off:fde=none:gs=on:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_1");
	quick.push("ott+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:sp=occurrence_290");
	quick.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_213");
	quick.push("ott+10_8:1_bs=off:bsr=on:nwc=4_77");
	quick.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=90_442");
	quick.push("ott+10_64_drc=off:nwc=1.1_298");
      }
      else if (atoms <= 20) {
	quick.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_111");
	quick.push("lrs+10_2:1_bs=off:drc=off:fsr=off:nwc=2.5:stl=60:sp=occurrence_14");
	quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_149");
	quick.push("ott+10_2_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.2:sp=reverse_arity_158");
	quick.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_275");
	quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_900");
      }
      else {
	quick.push("lrs+10_2:3_bs=unit_only:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=1:stl=20:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_61");
	quick.push("lrs+10_8_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=2:stl=120:urr=on_1148");
      }
    }
    else if (atoms <= 2) {
      quick.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_17");
      quick.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_1");
      quick.push("ins+4_8_bs=off:bfnt=on:br=off:cond=fast:flr=on:fsr=off:igbrr=0.1:igrr=1/128:igrp=100:igrpq=2.0:igwr=on:nwc=1.3:sos=all:urr=on_1");
      quick.push("ott+10_7_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=1.1:sp=occurrence_87");
      quick.push("lrs+10_1024_nwc=4:stl=150_1463");
    }
    else if (atoms <= 9) {
      quick.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_1");
      quick.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_3");
      quick.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_1");
      quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_852");
      quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_33");
      quick.push("ott+10_5_bd=off:drc=off:nwc=2.5_761");
      quick.push("dis+10_12_bs=off:br=off:ep=RSTC:fsr=off:nwc=4:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:urr=on_59");
    }
    else if (atoms <= 10) {
      quick.push("dis+11_16_bs=off:bfnt=on:fsr=off:fde=none:gs=on:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_1");
      quick.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.5_480");
      quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_328");
      quick.push("ott+10_2:1_drc=off:nwc=5_1146");
      quick.push("ott+10_2:3_drc=off:nwc=2_504");
      quick.push("ott+10_8:1_nwc=3:sfv=off_860");
    }
    else if (atoms <= 15) {
      quick.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_1");
      quick.push("lrs+10_14_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.2:stl=20:sio=off:sp=occurrence_25");
      quick.push("lrs+3_20_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:stl=120_313");
      quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_619");
      quick.push("ott+10_20_bd=off:drc=off:nwc=2:sp=occurrence_451");
    }
    else if (atoms <= 18) {
      quick.push("lrs+10_16_drc=off:nwc=1.2:stl=40_351");
      quick.push("dis+10_128_bs=unit_only:bsr=on:drc=off:fsr=off:nwc=2.5_295");
      quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_275");
      quick.push("ott+10_10_drc=off:fde=none:nwc=1.1:sp=occurrence_363");
    }
    else {
      quick.push("lrs+10_16_drc=off:nwc=1.2:stl=40_391");
      quick.push("lrs+10_5:1_nwc=1:stl=90_214");
      quick.push("ott+10_2_fde=none:nwc=2.5:sp=reverse_arity_728");
    }
    break;
  }

  switch (cat) {
  case Property::NEQ:
    quick.push("dis-1010_6_bs=off:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sos=all:sp=occurrence_300");
    quick.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_300");
    quick.push("dis+10_5_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sgo=on:sio=off:sp=occurrence_100");
    quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_300");
    quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_300");
    quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_300");
    quick.push("ott-1010_2:1_bs=off:cond=fast:drc=off:nwc=3:sd=1:ss=axioms:st=2.0:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("lrs+10_1_bs=off:cond=fast:nwc=5:sio=off:spl=sat:ssfq=1.1:ssnc=none_200");
    quick.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_300");
    quick.push("dis-11_10_bfnt=on:cond=fast:lcm=predicate:nwc=1.2:sio=off:spl=off:sp=occurrence_600");
    quick.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_300");
    quick.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_300");
    quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_300");
    quick.push("dis+11_4:1_bs=off:cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_300");
    quick.push("dis+1_40_bs=off:ep=RSTC:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none:urr=on_300");
    quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("dis+1011_24_cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_300");
    quick.push("ott+11_3:1_bs=off:drc=off:ep=on:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    quick.push("lrs+2_3:1_bs=off:br=off:cond=fast:drc=off:flr=on:nwc=4:sio=off:spo=on:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_600");
    quick.push("dis-11_28_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none_300");
    quick.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=700:igrpq=1.5:igwr=on:nwc=3:sos=on:sgo=on:sio=off_300");
    quick.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    quick.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_200");
    quick.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_600");
    quick.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_600");
    quick.push("dis+1011_2_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_300");
    quick.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_300");
    quick.push("lrs+2_64_bd=off:bs=off:br=off:cond=on:drc=off:flr=on:fde=none:nwc=1.7:sio=off:spl=sat:ssfp=1000:ssfq=1.4:ssnc=none:urr=on_300");
    quick.push("dis+10_3:1_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:spl=sat:sp=reverse_arity:urr=on:updr=off_300");
    quick.push("dis-1002_5:1_bs=off:cond=fast:drc=off:ep=on:nwc=1.1:sd=4:ss=axioms:sos=on:sio=off:spl=sat:urr=on_300");
    quick.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=2.5:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_300");
    quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=1.0:igrp=400:igrpq=1.5:nwc=5:sio=off_300");
    quick.push("dis+10_1024_bs=off:drc=off:flr=on:fsr=off:nwc=1.1:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_300");
    quick.push("dis+2_4:1_bs=unit_only:cond=on:flr=on:lcm=predicate:nwc=1:ssac=none:ssfp=100000:ssfq=2.0:ssnc=all:sfv=off:urr=on_300");
    quick.push("dis-11_1024_bs=off:bfnt=on:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:sp=occurrence:urr=on_300");
    quick.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("dis+10_10_bs=off:cond=fast:drc=off:gs=on:nwc=1.7:nicw=on:sd=1:ss=axioms:st=3.0_300");
    quick.push("dis+11_4_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=1.7:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_300");
    quick.push("ott+1011_3_bs=off:bsr=unit_only:fde=none:nwc=2:sio=off:spl=sat:ssfq=1.0:ssnc=none_300");
    quick.push("lrs+1010_24_bd=off:bs=off:cond=on:drc=off:gsp=input_only:nwc=1.3:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_100");
    quick.push("dis+3_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=10:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=reverse_arity_300");
    quick.push("dis-1_128_bfnt=on:fsr=off:nwc=1.5:nicw=on:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=all_500");
    quick.push("lrs+2_14_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:nwc=1.1:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_300");
    quick.push("dis-1002_3:2_bs=off:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_300");
    quick.push("dis+11_8:1_bs=off:drc=off:ep=RS:nwc=10:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_300");
    quick.push("ott+10_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:ssfq=2.0:ssnc=none_300");
    quick.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:sio=off:spl=sat:ssnc=none_300");
    quick.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_300");
    quick.push("ott-11_40_bd=off:bs=off:drc=off:flr=on:fsr=off:lcm=predicate:nwc=10:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:updr=off_300");
    quick.push("dis+3_4_bs=off:br=off:cond=on:drc=off:ep=RSTC:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on_100");
    quick.push("ins+1_3:1_bs=off:cond=on:ep=RSTC:flr=on:gs=on:igbrr=0.8:igrr=1/4:igrp=400:igrpq=1.1:igwr=on:nwc=1.5:sio=off:urr=on_300");
    quick.push("lrs+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off:sp=reverse_arity_300");
    quick.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_300");
    quick.push("dis+11_20_bs=off:cond=fast:fde=none:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_300");
    quick.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("ott+1_10_bd=off:bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    quick.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_300");
    quick.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    quick.push("ott+10_64_bd=off:bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    quick.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    quick.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_200");
    quick.push("dis-1002_12_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_300");
    quick.push("dis+1011_1024_bs=unit_only:drc=off:gsp=input_only:nwc=1.1:sio=off:spo=on:urr=on_300");
    quick.push("dis+1_2:1_bs=off:bsr=on:cond=fast:ep=RSTC:gs=on:lcm=predicate:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on_900");
    quick.push("lrs+4_24_bd=off:bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sio=off:spl=sat:ssfp=4000:ssfq=1.2:ssnc=none_600");
    break;

  case Property::HEQ:
    quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_600");
    quick.push("ins+4_12_bs=off:bfnt=on:cond=fast:gsp=input_only:igbrr=0.8:igrr=128/1:igrpq=2.0:nwc=1_300");
    quick.push("ott+11_128_bs=off:drc=off:gsp=input_only:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_900");
    quick.push("ott+11_16_bfnt=on:cond=fast:nwc=1.1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=2.0:sp=reverse_arity_1200");
    quick.push("lrs+2_4_bs=off:cond=fast:drc=off:gsp=input_only:nwc=4:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_900");
    quick.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=10:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_300");
    quick.push("dis+11_5:4_bs=off:cond=fast:drc=off:fde=none:nwc=1:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=none:urr=on_300");
    quick.push("ins+11_64_bs=off:cond=on:drc=off:fde=none:igbrr=0.2:igrr=1/64:igrp=400:igrpq=1.05:igwr=on:nwc=1.2:sio=off_900");
    quick.push("ott+2_16_bsr=unit_only:br=off:cond=on:flr=on:fsr=off:nwc=5:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sfv=off:urr=on:updr=off_900");
    quick.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=1:sio=off:spl=off_900");
    quick.push("lrs+11_3:1_bs=unit_only:drc=off:fde=none:nwc=10:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_600");
    quick.push("dis+10_1024_bd=off:bs=off:cond=on:drc=off:fde=none:nwc=2.5:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_300");
    quick.push("dis+10_2:3_bfnt=on:cond=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:sp=reverse_arity_100");
    quick.push("lrs-1_2_bs=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_300");
    quick.push("dis-1002_3_bs=off:cond=fast:drc=off:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    quick.push("dis+3_1024_bfnt=on:cond=fast:fsr=off:nwc=5:sio=off:spl=off_100");
    quick.push("ott+11_24_bd=off:bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    quick.push("ins+4_5:4_bs=off:br=off:cond=on:ep=RSTC:flr=on:fsr=off:igbrr=0.1:igrr=1/16:igrpq=1.0:igwr=on:nwc=2:urr=on_600");
    quick.push("ins+2_64_bs=off:cond=on:drc=off:flr=on:fde=none:igbrr=0.1:igrr=1/16:igrpq=1.3:igwr=on:nwc=1.7:sp=reverse_arity_1200");
    break;

  case Property::PEQ:
   quick.push("lrs+3_40_bs=unit_only:bsr=on:cond=on:drc=off:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on:updr=off_1000");
    quick.push("dis-3_28_bd=off:cond=on:nwc=1.5:sio=off_600");
    quick.push("ott+11_5_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_900");
    quick.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_300");
    quick.push("dis+1_1024_nwc=1.1:sio=off:spl=off:updr=off_400");
    quick.push("ins+1_8:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrpq=1.2:igwr=on:nwc=3:sos=all:sgo=on_300");
    quick.push("dis-1003_128_drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    quick.push("lrs+10_2:3_bd=off:cond=on:drc=off:flr=on:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_900");
    quick.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1500");
    quick.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_600");
    quick.push("ins+1_20_bsr=on:br=off:cond=fast:drc=off:fsr=off:fde=none:igbrr=0.3:igrr=1/32:igrp=4000:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.2:sgo=on:sio=off:sp=occurrence:urr=on_400");
    quick.push("dis+1_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("ott+2_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_300");
    quick.push("ott+3_4:1_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence:urr=on_300");
    quick.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:sac=on:sio=off_300");
    quick.push("dis-1004_1024_bs=off:cond=fast:drc=off:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("ott+11_2:3_bd=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:updr=off_300");
    quick.push("ott+3_128_bs=off:drc=off:nwc=1.1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_600");
    quick.push("dis+11_32_bd=off:bsr=on:fsr=off:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_600");
    quick.push("ins+10_1_bfnt=on:igbrr=0.8:igrp=400:igrpq=2.0:nwc=1.7:sio=off_1500");
    quick.push("lrs+4_14_cond=on:drc=off:flr=on:nwc=3:spl=sat:sser=off:ssnc=none_1800");
    break;

  case Property::EPR:
    quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_2100");
    quick.push("dis-10_5:4_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.1:sac=on:sio=off:spo=on_300");
    quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_300");
    quick.push("ins+3_50_bs=off:br=off:drc=off:igbrr=0.7:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=2:sp=occurrence:urr=on_600");
    quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_300");
    quick.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_900");
    quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_300");
    quick.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_300");
    quick.push("ins+2_128_bs=unit_only:drc=off:fsr=off:igbrr=1.0:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:sos=on:sio=off:sp=occurrence_300");
    quick.push("ins+3_128_bs=off:br=off:drc=off:igbrr=0.1:igrr=32/1:igrp=2000:igrpq=2.0:igwr=on:nwc=3:sos=all:sio=off:urr=on_300");
    quick.push("ins+3_14_bs=off:cond=on:drc=off:flr=on:igbrr=0.2:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:nwc=1:urr=on_300");
    quick.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("ins-10_14_bs=off:drc=off:fde=none:igbrr=0.9:igrr=1/4:igrp=2000:igrpq=2.0:igwr=on:nwc=1.5:sos=on:sgo=on:sio=off:updr=off_1800");
    break;

  case Property::HNE: 
    quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_300");
    quick.push("ott+11_8_bs=off:bfnt=on:cond=fast:nwc=1:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none_300");
    quick.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:sio=off:spo=on_900");
    quick.push("lrs+1_128_bs=off:cond=on:gs=on:nwc=4:nicw=on:sio=off_900");
    quick.push("dis+11_24_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_300");
    quick.push("dis-11_8:1_bs=off:nwc=2.5:sio=off:spl=off_300");
    quick.push("ott+1003_28_bs=off:cond=on:flr=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=off_300");
    quick.push("lrs+3_4_bs=off:cond=fast:flr=on:nwc=1:nicw=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("dis+11_2:3_bs=off:cond=fast:fsr=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("dis+2_5:4_cond=fast:flr=on:lcm=predicate:nwc=1.5:sio=off:spl=off_600");
    quick.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:sio=off:spl=sat:ssfq=2.0_1800");
    quick.push("dis+10_4_bs=off:nwc=5:sac=on:sio=off_200");
    quick.push("lrs+11_128_cond=fast:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:ssfp=100000:ssfq=2.0:ssnc=none_600");
    quick.push("ott+1_8:1_bs=off:cond=on:gs=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("lrs+10_8:1_bs=off:cond=fast:flr=on:fsr=off:nwc=2.5:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_900");
    quick.push("dis+1002_64_bs=off:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:nicw=on:sio=off:spo=on_600");
    break;

  case Property::NNE: 
    quick.push("dis+1011_12_bs=off:cond=fast:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_900");
    quick.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=2.0:nwc=4_300");
    quick.push("dis-1010_14_bsr=on:cond=on:nwc=1.5:sio=off:spl=sat:ssfp=100000:ssfq=1.1:ssnc=none_300");
    quick.push("ott+1_20_bfnt=on:cond=on:nwc=3:sac=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.4_300");
    quick.push("dis+1011_16_bs=unit_only:cond=on:fsr=off:gsp=input_only:nwc=1.7:sos=all:sgo=on:sio=off:spl=sat:ssfq=2.0:ssnc=all_200");
    quick.push("dis-11_40_bs=off:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssac=none:ssfp=40000:ssfq=2.0:ssnc=none_300");
    quick.push("ott+4_2:1_bs=off:cond=on:lcm=predicate:nwc=10:nicw=on:sac=on:sio=off_300");
    quick.push("dis-1_16_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1.2:nicw=on:ssfq=1.1:ssnc=none:sp=occurrence_100");
    quick.push("dis+1_28_bs=off:bfnt=on:cond=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.7:sio=off:spl=off:sp=occurrence_300");
    quick.push("ott-3_16_bs=off:gsp=input_only:nwc=2:nicw=on:sos=all:sio=off:spl=sat:ssnc=none_300");
    quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.7:igrpq=2.0:nwc=4_500");
    quick.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:sio=off:spl=sat:ssnc=none_300");
    quick.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("ott-1002_1024_cond=on:flr=on:gs=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none:urr=on_300");
    quick.push("dis+1011_50_bs=off:cond=fast:flr=on:gsp=input_only:nwc=1.3:sos=all_300");
    quick.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    quick.push("dis+1011_40_bs=off:gsp=input_only:nwc=4:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("ott+1011_5_bs=off:gs=on:nwc=2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssnc=none_100");
    quick.push("dis-2_16_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:sagn=off:sio=off:spl=sat:ssnc=none_300");
    break;

  case Property::FEQ: 
    quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_300");
    quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_300");
    quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_2700");
    quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_300");
    quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_900");
    quick.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_300");
    quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_2400");
    quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_300");
    quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_300");
    quick.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_300");
    quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_300");
    quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_300");
    quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_300");
    quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_300");
    quick.push("tab+10_1_ep=RST:gsp=input_only:sd=4:ss=axioms:st=2.0:sio=off:tbsr=off:tgawr=1/32:tglr=1/5:tipr=off:tlawr=8/1_100");
    quick.push("ins+3_10_bs=off:drc=off:fde=none:igbrr=0.8:igrr=1/128:igrp=100:igrpq=1.0:igwr=on:nwc=2.5:sio=off:spl=off_300");
    quick.push("ott+2_12_bd=off:drc=off:lcm=reverse:nwc=2:sio=off:spo=on_600");
    quick.push("ins+10_2:3_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=100:igrpq=1.0:igwr=on:nwc=2:sos=all:sio=off:urr=on_300");
    quick.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_300");
    quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_300");
    quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_300");
    quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_300");
    quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_300");
    quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    quick.push("dis+1_10_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=7:ss=axioms:st=1.5:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_400");
    quick.push("ott+1011_2_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_300");
    quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_300");
    quick.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_300");
    quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_600");
    quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_300");
    quick.push("lrs-1_10_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_200");
    quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_300");
    quick.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_500");
    quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_300");
    quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_300");
    quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_300");
    quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_300");
    quick.push("ott+4_32_bs=off:flr=on:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    quick.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_300");
    quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_300");
    quick.push("lrs+1_6_bs=off:drc=off:nwc=3:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_3600");
    quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_300");
    quick.push("dis+11_1024_bsr=unit_only:cond=fast:nwc=1.3:sio=off:spl=off_600");
    quick.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_300");
    quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_300");
    quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_300");
    quick.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_300");
    quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_300");
    quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_300");
    quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_300");
    quick.push("dis+4_40_cond=on:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_300");
    quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_300");
    quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_300");
    quick.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_300");
    quick.push("ott+10_3:1_bsr=unit_only:cond=fast:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on:updr=off_300");
    quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_300");
    quick.push("ott+11_24_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=reverse_arity_400");
    quick.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_300");
    quick.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_300");
    quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_300");
    quick.push("dis+11_10_bs=off:lcm=predicate:nwc=1.3:sio=off_300");
    quick.push("dis+10_2_bs=off:cond=on:drc=off:fde=none:lcm=predicate:nwc=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=reverse_arity_300");
    quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_300");
    quick.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:sio=off:spl=sat:urr=on_300");
    quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_300");
    quick.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_600");
    quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_800");
    quick.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_400");
    quick.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_600");
    quick.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_300");
    quick.push("dis-1010_50_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_900");
    quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_300");
    quick.push("dis+4_2:1_bs=off:br=off:drc=off:fsr=off:nwc=1:sos=all:sio=off:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_200");
    quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_300");
    quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_300");
    quick.push("dis+1010_32_cond=fast:drc=off:ep=RS:fsr=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    quick.push("ott+1011_10_bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_200");
    quick.push("lrs-1004_32_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_300");
    quick.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_300");
    quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_100");
    quick.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_300");
    quick.push("dis+1011_28_cond=on:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_100");
    quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_300");
    quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_300");
    quick.push("ott-3_10_bs=off:br=off:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_300");
    quick.push("dis+1003_1024_bs=off:drc=off:fsr=off:nwc=1.7:nicw=on:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_300");
    quick.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_300");
    quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_100");
    quick.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.5:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=reverse_arity_300");
    quick.push("ott+10_24_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssnc=none_300");
    quick.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_300");
    quick.push("ins+2_4:1_bs=off:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrpq=1.05:igwr=on:nwc=5:sos=on:sio=off:urr=on_300");
    quick.push("dis-1002_8:1_bs=off:cond=on:drc=off:flr=on:gs=on:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_300");
    quick.push("dis+11_28_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=5:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sp=occurrence_300");
    quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_300");
    quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_300");
    quick.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_300");
    quick.push("lrs-1004_12_bs=off:bsr=unit_only:drc=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none_600");
    quick.push("lrs-1002_3_bd=off:bs=off:drc=off:ep=on:nwc=1.7:sos=on:sac=on:sio=off_1500");
    quick.push("dis+1010_40_bs=off:drc=off:ep=RS:nwc=1:sio=off:spo=on:spl=sat:ssnc=none_300");
    quick.push("dis+1011_3_bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_300");
    quick.push("lrs+1_5_bs=off:cond=fast:drc=off:flr=on:nwc=10:sac=on:sio=off:urr=on_300");
    quick.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_300");
    quick.push("dis+1_14_bd=off:bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=4:sos=on:sio=off:spo=on:sp=reverse_arity_200");
    quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_300");
    quick.push("dis+2_20_drc=off:ep=RST:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_300");
    quick.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_300");
    quick.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_300");
    quick.push("lrs+1_64_bs=off:drc=off:gsp=input_only:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:updr=off_600");
    quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_300");
    quick.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_1200");
    quick.push("dis-1010_3:1_bd=off:bs=off:cond=fast:gs=on:lcm=reverse:nwc=1.1:sac=on_900");
    quick.push("ott+4_14_bs=unit_only:cond=fast:drc=off:nwc=1.2:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_600");
    quick.push("dis+2_16_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none_600");
    quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1200");
    quick.push("lrs-11_12_bs=off:drc=off:fde=none:gsp=input_only:gs=on:lcm=predicate:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sfv=off:sp=occurrence:urr=on:updr=off_3000");
    quick.push("ott+10_3:1_bd=off:drc=off:lcm=reverse:nwc=10:nicw=on:sio=off:spo=on:ssac=none:sscc=on:sser=off:ssfp=1000:ssfq=1.2:ssnc=all_900");
    quick.push("ott+4_64_bd=off:bs=off:br=off:cond=on:drc=off:fsr=off:gs=on:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:urr=on_900");
    break;

  case Property::FNE:
    quick.push("dis-1010_12_bs=off:bsr=unit_only:cond=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence:urr=on_300");
    quick.push("dis+11_50_bs=off:cond=on:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssnc=none:urr=on_300");
    quick.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    quick.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_600");
    quick.push("dis+11_50_bs=off:bsr=on:cond=on:lcm=reverse:nwc=1:sio=off:spl=sat:sser=off:ssnc=none:updr=off_300");
    quick.push("ott+1011_50_bs=off:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on:updr=off_300");
    quick.push("dis+4_128_bs=off:cond=on:flr=on:nwc=1.2:sos=on:sac=on_300");
    quick.push("dis+1004_10_bs=off:nwc=1.5:sagn=off:sio=off:spl=sat:ssnc=none_900");
    quick.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_300");
    quick.push("tab+10_1_spl=off:tbsr=off:tfsr=off:tgawr=3/1:tglr=1/20:tipr=off:tlawr=8/1_300");
    quick.push("ins+10_1_gsp=input_only:igbrr=0.9:igrp=100:igrpq=1.1:nwc=2_300");
    quick.push("ott-1002_3_bs=unit_only:bsr=unit_only:cond=on:gsp=input_only:nwc=1.2:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:urr=on_300");
    quick.push("ott+1_40_bsr=unit_only:cond=fast:gs=on:nwc=1.5:sio=off:spl=sat:ssnc=none:urr=on_300");
    quick.push("dis+3_6_flr=on:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence_300");
    quick.push("dis+1010_8_bs=off:nwc=1.1:sio=off_300");
    quick.push("ott-1010_128_bs=off:cond=on:lcm=predicate:nwc=1.3:urr=on_600");
    quick.push("ott+10_1024_bs=off:fsr=off:nwc=1.5:nicw=on:sio=off:spl=off_1200");
    quick.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:spo=on_1200");
    break;

  case Property::UEQ:
    quick.push("lrs+10_8_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=2:urr=on_1200");
    quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5_1800");
    quick.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_300");
    quick.push("lrs+10_1024_nwc=4_1500");
    quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_600");
    quick.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.5_600");
    quick.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_300");
    quick.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_200");
    quick.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2_900");
    quick.push("dis+2_14_bs=off:br=off:ep=RSTC:flr=on:fsr=off:nwc=2.5:nicw=on:sos=all:sio=off:spl=sat:ssnc=none:urr=on_100");
    quick.push("lrs+10_5:1_nwc=1_900");
    quick.push("lrs+10_2:3_bs=unit_only:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_200");
    quick.push("ott+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:sp=occurrence_600");
    quick.push("ott+10_8:1_bs=off:bsr=on:nwc=4_300");
    quick.push("ott+10_64_drc=off:nwc=1.1_400");
    quick.push("ott+10_2:1_drc=off:nwc=5_1200");
    quick.push("ott+10_20_bd=off:drc=off:nwc=2:sp=occurrence_600");
    quick.push("ott+10_2:3_drc=off:nwc=2_600");
    quick.push("ott+10_5_bd=off:drc=off:nwc=2.5_900");
    quick.push("ott+10_2_fde=none:nwc=2.5:sp=reverse_arity_900");
    quick.push("ott+10_8:1_nwc=3:sfv=off_900");
    break;
  }

  StrategySet usedSlices;
  if (runSchedule(quick,usedSlices,false,terminationTime)) {
    return;
  }
  //  if (env.timer->elapsedMilliseconds() >= terminationTime) {
  //    return;
  //  }
  //  runSchedule(fallback,usedSlices,true,terminationTime);
} // CLTBProblem::performStrategy(int terminationTime)

/**
 * This function solves a single problem. It parses the problem, spawns a
 * writer process for output and creates a pipe to communicate with it.
 * Then it calls performStrategy(terminationTime) that performs the
 * actual proof search.
 * @param terminationTime the time in milliseconds since the prover start
 * @since 04/06/2013 flight Manchester-Frankfurt
 * @author Andrei Voronkov
 */
void CLTBProblem::searchForProof(int terminationTime)
{
  CALL("CLTBProblem::searchForProof");

  System::registerForSIGHUPOnParentDeath();

  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  env.options->setInputFile(problemFile);
  // this local scope will delete a potentially large parser
  {
    TimeCounter tc(TC_PARSING);
    env.statistics->phase=Statistics::PARSING;

    ifstream inp(problemFile.c_str());
    if (inp.fail()) {
      USER_ERROR("Cannot open problem file: " + problemFile);
    }
    Parse::TPTP parser(inp);
    List<vstring>::Iterator iit(parent->_theoryIncludes);
    while (iit.hasNext()) {
      parser.addForbiddenInclude(iit.next());
    }
    parser.parse();
    UnitList* probUnits = parser.units();
    UIHelper::setConjecturePresence(parser.containsConjecture());
    prb.addUnits(probUnits);
  }

  if (prb.getProperty()->atoms()<=1000000) {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation norm;
    norm.normalise(prb);
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  //fork off the writer child process
  writerChildPid = Multiprocessing::instance()->fork();
  if (!writerChildPid) { // child process
    runWriterChild();
    ASSERTION_VIOLATION; // the runWriterChild() function should never return
  }
  CLTBMode::coutLineOutput() << "writer pid " << writerChildPid << endl << flush;

  //when the pipe will be closed, we want the process to terminate properly
  signal(SIGPIPE, &terminatingSignalHandler);

  //only the writer child is reading from the pipe (and it is now forked off)
  childOutputPipe.neverRead();
  env.setPipeOutput(&childOutputPipe); //direct output into the pipe
  UIHelper::cascMode=true;

  performStrategy(terminationTime);
  exitOnNoSuccess();
  ASSERTION_VIOLATION; // the exitOnNoSuccess() function should never return
} // CLTBProblem::perform

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
  CLTBMode::lineOutput() << "Proof not found in time " << Timer::msToSecondsString(env.timer->elapsedMilliseconds()) << endl;
  if (env.remainingTime()/100>0) {
    CLTBMode::lineOutput() << "SZS status GaveUp for " << env.options->problemName() << endl;
  }
  else {
    //From time to time we may also be terminating in the timeLimitReached()
    //function in Lib/Timer.cpp in case the time runs out. We, however, output
    //the same string there as well.
    CLTBMode::lineOutput() << "SZS status Timeout for " << env.options->problemName() << endl;
  }
  env.endOutput();

  env.setPipeOutput(0);
  //This should make the writer child terminate.
  childOutputPipe.neverWrite();

  try {
    int writerResult;
    Multiprocessing::instance()->waitForParticularChildTermination(writerChildPid, writerResult);
    ASS_EQ(writerResult,0);
  }
  catch (SystemFailException& ex) {
    //it may happen that the writer process has already exitted
    if (ex.err!=ECHILD) {
      throw;
    }
  }

  CLTBMode::coutLineOutput() << "problem proof search terminated (fail)" << endl << flush;
  System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
} // CLTBProblem::exitOnNoSuccess

/**
 * Run a schedule. Terminate the process with 0 exit status
 * if a proof was found, otherwise return false. This function available cores:
 * If the total number of cores @b n is 8 or more, then @b n-2, otherwise @b n-1.
 * It spawns processes by calling runSlice()
 * @author Andrei Voronkov
 * @since 04/06/2013 flight Frankfurt-Vienna, updated for CASC-J6
 */
bool CLTBProblem::runSchedule(Schedule& schedule,StrategySet& used,bool fallback,int terminationTime)
{
  CALL("CLTBProblem::runSchedule");

  // compute the number of parallel processes depending on the
  // number of available cores
  int parallelProcesses;
  unsigned coreNumber = System::getNumberOfCores();
  if (coreNumber <= 1) {
    parallelProcesses = 1;
  }
  else if (coreNumber>=8) {
    parallelProcesses = coreNumber-2;
  }
  else {
    parallelProcesses = coreNumber-1;
  }

  int processesLeft = parallelProcesses;
  Schedule::BottomFirstIterator it(schedule);
 
  int slices = schedule.length();
  while (it.hasNext()) {
    while (processesLeft) {
      CLTBMode::coutLineOutput() << "Slices left: " << slices-- << endl;
      CLTBMode::coutLineOutput() << "Processes available: " << processesLeft << endl << flush;
      ASS_G(processesLeft,0);

      int elapsedTime = env.timer->elapsedMilliseconds();
      if (elapsedTime >= terminationTime) {
	// time limit reached
        return false;
      }
 
      vstring sliceCode = it.next();
      vstring chopped;

      // slice time in milliseconds
      int sliceTime = SLOWNESS * getSliceTime(sliceCode,chopped);
      if (used.contains(chopped)) {
	// this slice was already used
	continue;
      }
      used.insert(chopped);
      int remainingTime = terminationTime - elapsedTime;
      if (sliceTime > remainingTime) {
	sliceTime = remainingTime;
      }

      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if (!childId) {
        //we're in a proving child
        try {
          runSlice(sliceCode,sliceTime); //start proving
        } catch (Exception& exc) {
          cerr << "% Exception at run slice level" << endl;
          exc.cry(cerr);
          System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
        }
        ASSERTION_VIOLATION; //the runSlice function should never return
      }
      Timer::syncClock();
      ASS(childIds.insert(childId));
      CLTBMode::coutLineOutput() << "slice pid "<< childId << " slice: " << sliceCode
				 << " time: " << (sliceTime/100)/10.0 << endl << flush;
      processesLeft--;
      if (!it.hasNext()) {
	break;
      }
    }

    CLTBMode::coutLineOutput() << "No processes available: " << endl << flush;
    if (processesLeft==0) {
      waitForChildAndExitWhenProofFound();
      // proof search failed
      processesLeft++;
    }
  }

  while (parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    waitForChildAndExitWhenProofFound();
    // proof search failed
    processesLeft++;
    Timer::syncClock();
  }
  return false;
} // CLTBProblem::runSchedule

/**
 * Wait for termination of a child and terminate the process with a zero status
 * if a proof was found. If the child didn't find the proof, just return.
 */
void CLTBProblem::waitForChildAndExitWhenProofFound()
{
  CALL("CLTBProblem::waitForChildAndExitWhenProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
  if (finishedChild == writerChildPid) {
    finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
  }
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if (!resValue) {
    // we have found the proof. It has been already written down by the writter child,
    // so we can just terminate
    CLTBMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (success)" << endl << flush;
    int writerResult;
    try {
      Multiprocessing::instance()->waitForParticularChildTermination(writerChildPid, writerResult);
    }
    catch (SystemFailException& ex) {
      //it may happen that the writer process has already exitted
      if (ex.err!=ECHILD) {
	throw;
      }
    }
    System::terminateImmediately(0);
  }
  // proof not found
  CLTBMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (fail)" << endl << flush;
} // waitForChildAndExitWhenProofFound

ofstream* CLTBProblem::writerFileStream = 0;

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
//  Timer::setTimeLimitEnforcement(false);

  // This was the previous code, now removed: we assume that this child has all the time it needs
  // Timer::setTimeLimitEnforcement(true);
  // int writerLimit = parent->_problemTimeLimit+env.timer->elapsedSeconds()+2;
  // env.options->setTimeLimitInSeconds(writerLimit);

  //we're in the child that writes down the output of other children
  childOutputPipe.neverWrite();

  ofstream out(outFile.c_str());

  writerFileStream = &out;
  childOutputPipe.acquireRead();

  while (!childOutputPipe.in().eof()) {
    vstring line;
    getline(childOutputPipe.in(), line);
    if (line == problemFinishedString) {
      break;
    }
    out << line << endl << flush;
  }
  out.close();
  writerFileStream = 0;

  childOutputPipe.releaseRead();
  System::terminateImmediately(0);
}

void CLTBProblem::terminatingSignalHandler(int sigNum)
{
  if (writerFileStream) {
    writerFileStream->close();
  }
  System::terminateImmediately(0);
}

/**
 * Run a slice given by its code using the specified time limit.
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
void CLTBProblem::runSlice(vstring sliceCode, unsigned timeLimitInMilliseconds)
{
  CALL("CLTBProblem::runSlice");

  Options opt = *env.options;
  opt.readFromEncodedOptions(sliceCode);
  opt.setTimeLimitInDeciseconds(timeLimitInMilliseconds/100);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  runSlice(opt);
} // runSlice

/**
 * Run a slice given by its options
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
void CLTBProblem::runSlice(Options& strategyOpt)
{
  CALL("CLTBProblem::runSlice(Option&)");

  System::registerForSIGHUPOnParentDeath();
  UIHelper::cascModeChild=true;

  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();
  Timer::setTimeLimitEnforcement(true);

  Options opt = strategyOpt;
  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  opt.setProblemName(problemFile);
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving

//  if (env.options->sineSelection()!=Options::SS_OFF) {
//    //add selected axioms from the theory
//    parent->theorySelector.perform(probUnits);
//
//    env.options->setSineSelection(Options::SS_OFF);
//    env.options->forceIncompleteness();
//  }
//  else {
//    //if there wasn't any sine selection, just put in all theory axioms
//    probUnits=UnitList::concat(probUnits, parent->theoryAxioms);
//  }

  env.beginOutput();
  CLTBMode::lineOutput() << opt.testId() << " on " << opt.problemName() << endl;
  env.endOutput();

  ProvingHelper::runVampire(prb, opt);

  //set return value to zero if we were successful
  if (env.statistics->terminationReason == Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  if (resultValue == 0) {
    env.out() << endl << problemFinishedString << endl << flush;
  }
  env.endOutput();
  exit(resultValue);
} // CLTBProblem::runSlice

/**
 * Return the intended slice time in milliseconds and assign the slice
 * vstring with chopped time limit to @b chopped.
 * @since 04/06/2013 flight Frankfurt-Vienna
 * @author Andrei Voronkov
 */
unsigned CLTBProblem::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos = sliceCode.find_last_of('_');
  vstring sliceTimeStr = sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = sliceTime + 1;
  if (time < 10) {
    time++;
  }
  // convert deciseconds to milliseconds
  return time * 100;
} // getSliceTime

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to env.out(). Returns env.out()
 * @since 05/06/2013 Vienna
 * @author Andrei Voronkov
 */
ostream& CLTBMode::lineOutput()
{
  CALL("CLTBMode::lineOutput");
  return env.out() << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CLTBMode::lineOutput

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to cout. Returns cout
 * @since 05/06/2013 Vienna
 * @author Andrei Voronkov
 */
ostream& CLTBMode::coutLineOutput()
{
  CALL("CLTBMode::lineOutput");
  return cout << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CLTBMode::coutLineOutput

#endif //!COMPILER_MSVC
